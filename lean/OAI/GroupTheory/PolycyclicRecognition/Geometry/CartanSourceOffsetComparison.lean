import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceCell
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinkedProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The offset comparison for the actual tiled and linked probes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open MeasureTheory Filter
open scoped Manifold Pointwise Topology NNReal

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))


local notation "ZQ" => TiledProbeChainData.sourceQuotientCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale)
    (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D)
    (Q := Q) (chartQ := chartQ)
local notation "J" => fun n => TiledProbeChainData.sourceKernelCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI)
    (E := E) (β := β) (scale := scale) (ι := ι) (Q := Q)
    (πQ := πQ) (hι := hι) (hrange := hrange) n

local notation "Y" => fun n => Set.prod ZQ (J n)
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)


variable [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [MeasurableMul F.D.carrier]
  [IsTopologicalGroup F.N.carrier] [IsTopologicalGroup Q.carrier]
  [SecondCountableTopology Q.carrier]
  {QT Z : Type*} [Group QT] [TopologicalSpace QT] [IsTopologicalGroup QT]
  [SecondCountableTopology QT] [MeasurableSpace QT] [BorelSpace QT]

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- Specialization to the actual tiled source cell with group-valued geometry. -/
theorem TiledProbeChainData.offset_nonpos_of_source_geometry
    (πT : F.N.carrier →* QT) (hπT : Continuous πT)
    (μT : Measure QT) (μTI : Measure πT.ker)
    (μ : Measure F.N.carrier) (ν : Measure F.D.carrier)
    [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite ν]
    [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
    (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
    (hscale : Tendsto scale atTop atTop) (hscale0 : ∀ n, 0 < scale n)
    (P₂ : ℝ) (regions : MeasuredProbeRegions πT μT μTI ν scale P₂)
    (hμ : μ = Measure.map (quotientSectionHomeomorph πT hπT
      regions.sectionMap regions.section_rightInverse).symm (μT.prod μTI))
    (hπQ : Continuous πQ)
    (μQS : Measure Q.carrier) (μIS : Measure πQ.ker) (μS : Measure F.N.carrier)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (F.action d) μS μS)
    (hσ : ∀ q, πQ (σ q) = q)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πQ hπQ σ hσ).symm
      (μQS.prod μIS))
    (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier)
    (hS : ∀ n, MeasurePreserving (S n) μS μS)
    (u k : ℕ → F.N.carrier)
    (length : Fin 3 → ℕ)
    (vertex : ∀ j n, (ZQ ×ˢ J n) → Fin (length j + 1) → F.N.carrier)
    (hstart : ∀ n y, vertex 0 n y 0 = u n)
    (hthird : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (length 1)))
    (hfirst : ∀ n y, vertex 0 n y (Fin.last (length 0)) =
      u n * S n ((y.val.2 : F.N.carrier) * σ y.val.1))
    (hanchor : ∀ n y, vertex 1 n y (Fin.last (length 1)) =
      coneProbeSecond (S n).toMulEquiv (u n)
        (ι (anchor n (D.index n (ψ n y).2))) (k n))
    (hsecond : ∀ n y, vertex 2 n y (Fin.last (length 2)) =
      coneProbeSecond (S n).toMulEquiv (u n) (y.val.2 : F.N.carrier) (k n))
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (good : ∀ n, Set (ZQ ×ˢ J n)) (hgood : ∀ n, IsCompact (good n))
    (hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)) (good n))
    (P₁ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (height : G →* Multiplicative W) (center : ℕ → G) (sample : ℕ → F.N.carrier)
    {Λ : ℝ≥0} (hΛ : 0 < (Λ : ℝ)) (p : ℕ → NormalizedPair G Λ)
    (d : ℕ → F.D.carrier) (chart : ℕ → Z → G) (q : Z → W) (z₀ : ℕ → Z)
    (A : W →ₗ[ℝ] W) (b : Bool → W) (hchart : ∀ n, chart n (z₀ n) = F.inclusionD (d n))
    (cell : Set (F.N.carrier × F.D.carrier)) (hcellm : MeasurableSet cell)
    (hcell0 : (μ.prod ν) cell ≠ 0) (hcelltop : (μ.prod ν) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n) (hη : Tendsto η atTop (𝓝 0))
    (δ Cp Dbridge : ℝ) (Et : Fin 3 → Set W) (hδ : 0 < δ)
    (hD : (Λ : ℝ) * Dbridge ≤ δ)
    (hpaths : ∀ᶠ n in atTop, regions.ControlsTwoPaths
      (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
      height cell (Et 0) (Et 2) (fun n => 2 * η n) Cp Cp δ n)
    (hbaseProfiles : ∀ᶠ n in atTop, ∀ s : Bool,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (F.inclusionN (sample n * if s then u n * S n (k n) else u n))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b s)‖ ≤ η n)
    (hprefixProfiles : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ j l,
      ‖rescaledMapProfile (fun g => (height ((p n).val.1 g)).toAdd) (center n)
        (F.inclusionN (sample n * vertex j n y l))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + b (j != 0))‖ ≤ 2 * η n)
    (hbridge : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (center n * F.inclusionN
          (sample n * coneProbeSecond (S n).toMulEquiv (u n) (y.val.2 : F.N.carrier) (k n)) *
          chart n (z₀ n))
        (center n * F.inclusionN (sample n * vertex 0 n y (Fin.last (length 0))) *
          chart n (z₀ n)) ≤ Dbridge * scale n)
    (hprobePaths : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ j,
      ∃ path : Path (1 : G) (basedImage (p n).val.1
        (center n * F.inclusionN (sample n * vertex j n y 0) * chart n (z₀ n))
        (center n * F.inclusionN (sample n * vertex j n y (Fin.last (length j))) * chart n (z₀ n))),
        PathMetricBound path (Cp * scale n) (Cp * (1 + Real.log (2 + scale n))) ∧
        ∀ t, ∃ w ∈ Et j, ‖(height (path t)).toAdd - scale n • w‖ ≤
          4 * scale n * η n + Cp * (1 + Real.log (2 + scale n)))
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (height g).toAdd)) * μT E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (b true - b false) ≤ 0 := by
  exact MeasuredProbeRegions.offset_nonpos_of_linked_probe_bounds
    (N := F.N.carrier) (D := F.D.carrier) (G := G) (Q := QT)
    (W := W) (V := W) (Z := Z)
    πT hπT μT μTI μ ν F.action F.inclusionN F.inclusionD F.conjugation hφ
    actionQ act hact scale hscale hscale0 P₂ regions hμ πQ hπQ μQS μIS μS hφS σ hσ hμS
    (fun n => (S n).toHomeomorph) hS F.closedN hΛ p d ZQ J hZm hJm hZ0 hZt hJ0 hJt
    good hgood hmass P₁ hv hvol tiles (fun n y => D.index n (ψ n y).2)
    height center sample u (fun n => u n * S n (k n))
    (fun n l => coneProbeSecond (S n).toMulEquiv (u n) (ι (anchor n l)) (k n))
    (fun n y => coneProbeSecond (S n).toMulEquiv (u n) (y.val.2 : F.N.carrier) (k n))
    length vertex hstart hthird hfirst hanchor hsecond
    chart q z₀ A b hchart cell hcellm hcell0 hcelltop hsmall F.surjective
    η hη0 hη δ Cp Dbridge Et hδ (fun n => (p n).property.1.1) hD hpaths
    hbaseProfiles hprefixProfiles hbridge hprobePaths ell tileLoss htileLoss htile0 hHaar htiles

end PolycyclicRecognition.CartanWordModel

end

end OAI
