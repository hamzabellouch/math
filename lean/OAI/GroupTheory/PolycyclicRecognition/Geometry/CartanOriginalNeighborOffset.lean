import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinkedProbeOffset
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOriginalNeighborFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRestrictedNeighborLaw
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledProbeFrames
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfilePivot
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConcentratedProbeSelection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedProfileSelection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPivotProbePaths
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeInteriorHeights

namespace OAI

/-! # A trace comparison from the original neighboring-cell law -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set TopologicalSpace
open scoped Manifold Topology NNReal ENNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) [Fintype I] [DecidableEq I]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

variable [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

variable [IsTopologicalGroup F.N.carrier]


variable {QS QT : Type*}
  [Group QS] [TopologicalSpace QS] [IsTopologicalGroup QS] [T2Space QS]
  [SecondCountableTopology QS] [MeasurableSpace QS] [BorelSpace QS]
  [Group QT] [TopologicalSpace QT] [IsTopologicalGroup QT]
  [SecondCountableTopology QT] [MeasurableSpace QT] [BorelSpace QT]
  [MeasurableMul F.D.carrier]
  (πS : F.N.carrier →* QS) (ZQ : Set QS) (J : ℕ → Set πS.ker)
  [∀ n, CompactSpace (ZQ ×ˢ J n)] [∀ n, Nonempty (ZQ ×ˢ J n)]

/-- Concentrate the original law, then compare its actual linked probes.
All source cells and their volume/count bounds remain explicit. -/
theorem original_neighbor_offset_nonpos
    [Nonempty (Fin M.letterCount)]
    [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {E : Set W} (hE : IsCompact E) (hne : E.Nonempty) (β γ : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    (hweights : ∀ i, 0 < (M.supportIn T hunimod eW).weightSupport E i)
    {δ c lo hi : ℝ} (hδ : 0 < δ) (hc : 0 ≤ c) (hhi : 0 ≤ hi) (ht : 0 ≤ 1 - c * δ)
    (hcost : ∀ w : M.wordList,
      lo ≤ M.boxCost T hunimod eW E w ∧ M.boxCost T hunimod eW E w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hmono : StrictMono scale) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε : ℕ → ℝ) (hεpos : ∀ r, 0 ≤ ε r) (hε : Tendsto ε atTop (𝓝 0))
    (Eprobe : Fin 3 → Set W)
    (probe : Fin 3 → ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
    (P : ∀ k, M.BoxProbeChains T F hunimod eW b₀ (Eprobe k) β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i) scale (probe k))
    (origin base : ℕ → cartanRootIdeal H)
    (D : M.LinkedProbeChains T F hunimod eW b₀ Eprobe β
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport E i)
      scale probe P (fun n _ => origin n) (fun n _ => base n) ε)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (p : ℕ → NormalizedPair G Λ) (x : ℕ → G)
    (hN : Continuous F.ExpN) (hD : Continuous F.ExpD)
    (pivot : H) (V : Set W) (hV : IsOpen V) (hVconv : Convex ℝ V)
    (hEc : ∀ k, IsCompact (Eprobe k)) (hEconv : ∀ k, Convex ℝ (Eprobe k))
    (hpivot : ∀ k, eW (heightProjection T.character pivot) ∈ Eprobe k)
    (hEV : ∀ k, Eprobe k ⊆ V)
    (hVheight : V ⊆ (fun w => (1 - c * δ) • w) '' E)
    (σ : Fin M.letterCount → Bool)
    (hσ : (weightChamber (fun i =>
      ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap) σ).Nonempty)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (baseGroup step : ℕ → F.N.carrier)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = baseGroup n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = baseGroup n * step n)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)]
    (profile : ℕ → F.N.carrier → S) (hp : ∀ n, Measurable (profile n))
    (hactual : ∀ n q, q ∈ (fun v => v * baseGroup n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 ∪
      (fun v => v * baseGroup n * step n) ''
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1 → ∀ z,
      (profile n q).val z = rescaledMapProfile
        (fun g => (π ((p n).val.1 g)).toAdd) (x n) (F.inclusionN q)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z)
    (law : ProbabilityMeasure (S × S))
    (hlaw : Tendsto (fun n => ProbabilityMeasure.map
      (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN b₀
        E β (scale n) (baseGroup n)) (fun q => (profile n q, profile n (q * step n))))
      atTop (𝓝 law))
    (A : W →ₗ[ℝ] W) (bval : Bool → W) (f : S × S)
    (hf : f ∈ (law : Measure (S × S)).support)
    (haffine : ∀ s z,
      eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ V →
      (if s then f.2 else f.1).val z = A (eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G))) + bval s)
    (hπS : Continuous πS) (σS : C(QS, F.N.carrier))
    (hσS : ∀ q, πS (σS q) = q)
    (μQS : Measure QS) (μIS : Measure πS.ker) (μS : Measure F.N.carrier)
    [SFinite μQS] [SFinite μIS] [μS.IsMulLeftInvariant]
    [μIS.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μS]
    (hφS : ∀ d, MeasurePreserving (F.action d) μS μS)
    (hμS : μS = Measure.map (quotientSectionHomeomorph πS hπS σS hσS).symm
      (μQS.prod μIS))
    (flow : ℕ → F.N.carrier ≃ₜ F.N.carrier)
    (hflow : ∀ n, MeasurePreserving (flow n) μS μS)
    (hZm : MeasurableSet ZQ) (hJm : ∀ n, MeasurableSet (J n))
    (hZ0 : μQS ZQ ≠ 0) (hZt : μQS ZQ ≠ ⊤)
    (hJ0 : ∀ n, μIS (J n) ≠ 0) (hJt : ∀ n, μIS (J n) ≠ ⊤)
    (hregular : ∀ n,
      (cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n) (hZm.prod (hJm n))
        (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
        (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n)) :
          Measure (ZQ ×ˢ J n)).InnerRegular)
    (P₁ P₂ : ℝ) {v : ℝ} (hv : 0 < v)
    (hvol : ∀ n, v * Real.exp (scale n * P₁) ≤ (μIS (J n)).toReal)
    (tiles : ℕ → ℕ) (tile : ∀ n, (ZQ ×ˢ J n) → Fin (tiles n))
    (anchorRoot : ∀ n, Fin (tiles n) → F.N.carrier)
    (secondRoot : ∀ n, (ZQ ×ˢ J n) → F.N.carrier)
    (hfirst : ∀ n y, F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length))) =
      baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1))
    (hanchor : ∀ n y, F.ExpN (F.N.equiv (D.vertex 1 n y (Fin.last (P 1).length))) =
      anchorRoot n (tile n y))
    (hsecond : ∀ n y, F.ExpN (F.N.equiv (D.vertex 2 n y (Fin.last (P 2).length))) =
      secondRoot n y)
    (Dbridge δtarget : ℝ) (hδtarget : 0 < δtarget)
    (hDb : (Λ : ℝ) * Dbridge ≤ δtarget)
    (hbridge : ∀ᶠ n in atTop, ∀ y : ZQ ×ˢ J n,
      dist (F.inclusionN (secondRoot n y) * Exp (scale n •
          (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
        (F.inclusionN (baseGroup n * flow n ((y.val.2 : F.N.carrier) * σS y.val.1)) *
          Exp (scale n • (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ Dbridge * scale n)
    (πT : F.N.carrier →* QT) (hπT : Continuous πT)
    (μT : Measure QT) (μTI : Measure πT.ker)
    (μ : Measure F.N.carrier) (νD : Measure F.D.carrier)
    [SFinite μT] [SFinite μTI] [SFinite μ] [SFinite νD]
    [μT.IsMulLeftInvariant] [μ.IsMulLeftInvariant] [νD.IsMulLeftInvariant]
    (hφ : ∀ d, MeasurePreserving (F.action d) μ μ)
    (actionQ : F.D.carrier →* MulAut QT) (act : G →* Equiv.Perm QT)
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = πT u * actionQ d q)
    (cell : Set (F.N.carrier × F.D.carrier)) (hcell : MeasurableSet cell)
    (hcell0 : (μ.prod νD) cell ≠ 0) (hcelltop : (μ.prod νD) cell ≠ ⊤)
    (hsmall : ∀ z ∈ cell, dist (1 : G) (F.inclusionN z.1 * F.inclusionD z.2) < 1 / 2)
    (regionFactory : ∀ (η : ℕ → ℝ), (∀ n, 0 ≤ η n) → Tendsto η atTop (𝓝 0) →
      ∀ Cp : ℝ, 0 ≤ Cp → ∃ R : MeasuredProbeRegions πT μT μTI νD scale P₂,
        μ = Measure.map (quotientSectionHomeomorph πT hπT
          R.sectionMap R.section_rightInverse).symm (μT.prod μTI) ∧
        ∀ᶠ n in atTop, R.ControlsTwoPaths
          (fun u d => F.inclusionN u * F.inclusionD d) F.action (fun g q => act g q)
          π cell
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 0)
          ((fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe 2)
          (fun n => 2 * η n) Cp Cp δtarget n)
    (ell : W →L[ℝ] ℝ) (tileLoss : ℕ → ℝ)
    (htileLoss : HasSubexponentialUpperBoundSeq scale tileLoss)
    (htile0 : ∀ᶠ n in atTop, 0 ≤ tileLoss n)
    (hHaar : ∀ (g : G) (E : Set QT), μT (act g '' E) =
      ENNReal.ofReal (Real.exp (ell (π g).toAdd)) * μT E)
    (htiles : ∀ᶠ n in atTop,
      (tiles n : ℝ) ≤ tileLoss n * Real.exp (scale n * (P₁ - P₂))) :
    ell (bval true - bval false) ≤ 0 := by
  obtain ⟨Z, Cp, hZ, hZV, hCp, z₀, hz₀, frames⟩ :=
    M.exists_original_neighbor_root_frames T F hunimod eW hExp realize haarN haarD
      dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath b₀ hE hne β γ hβ hweights
      hδ hc hhi ht hcost hgap X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      scale hscale hmono hscale1 ε hεpos hε Eprobe probe P origin base D rem hdim p x
      hN hD pivot V hV hVconv hEc hEconv hpivot hEV hVheight σ hσ
      chartN hchartN baseGroup step horigin hbase S profile hp hactual law hlaw A bval f hf haffine
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let : MeasurableSpace C(Z, W) := borel _
  let : BorelSpace C(Z, W) := ⟨rfl⟩
  let : MeasurableSpace (C(Z, W) × C(Z, W)) := borel _
  let : BorelSpace (C(Z, W) × C(Z, W)) := ⟨rfl⟩
  let ν := fun n => cellSubtypeProbability (μQS.prod μIS) (ZQ ×ˢ J n)
    (hZm.prod (hJm n))
    (by rw [Measure.prod_prod]; exact mul_ne_zero hZ0 (hJ0 n))
    (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hZt (hJt n))
  let : ∀ n, (ν n : Measure (ZQ ×ˢ J n)).InnerRegular := hregular
  obtain ⟨η, sample, good, hη0, hη, hgood, hframes⟩ := frames ν
  let ηnonneg := fun n => (hη0 n).le
  obtain ⟨regions, hμ, hregions⟩ := regionFactory η ηnonneg hη Cp hCp
  let br := fun n => exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
  let chart := fun n (z : Z) => F.profileChart (br n) z.val
  let q := fun z : Z => eW (heightProjection T.character
    ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z.val :
      GroupLieAlgebra (𝓘(ℝ, EG)) G))
  let dseq := fun n => F.ExpD (F.D.equiv ((br n).equivFun.symm (z₀ n).val))
  let sampled := fun n => F.sampleRoot (M.boxBasis T hunimod eW E β (scale n)) (sample n)
  let vertex := fun j n y l => F.ExpN (F.N.equiv (D.vertex j n y l))
  have hchart : ∀ n, chart n (z₀ n) = F.inclusionD (dseq n) := fun _ => rfl
  have hstart : ∀ n y, vertex 0 n y 0 = baseGroup n := by
    intro n y
    exact (congrArg (fun v => F.ExpN (F.N.equiv v)) (D.first_start n y)).trans (horigin n)
  have hthird : ∀ n y, vertex 2 n y 0 = vertex 1 n y (Fin.last (P 1).length) := by
    intro n y
    exact congrArg (fun v => F.ExpN (F.N.equiv v)) (D.third_start n y)
  have hmass : ∀ n, ENNReal.ofReal (1 / 4 : ℝ) ≤ (ν n : Measure _) (good n) := by
    intro n
    have he : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 4 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    simpa only [he] using (hgood n).2.2.le
  have hbaseProfiles : ∀ᶠ n in atTop, ∀ s : Bool,
      ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (sampled n * if s then baseGroup n * step n else baseGroup n))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + bval s)‖ ≤ η n := by
    filter_upwards [hframes] with n hn s
    cases s with
    | false => simpa [sampled, chart, br, q, horigin] using (hn.1 false).le
    | true => simpa [sampled, chart, br, q, hbase] using (hn.1 true).le
  have hprefix : ∀ᶠ n in atTop, ∀ y ∈ good n, ∀ j l,
      ‖rescaledMapProfile (fun g => (π ((p n).val.1 g)).toAdd) (x n)
        (F.inclusionN (sampled n * vertex j n y l))
        (Real.log (scale n)) (chart n) (z₀ n) - (A (q (z₀ n)) + bval (j != 0))‖ ≤ 2 * η n := by
    filter_upwards [hframes] with n hn y hy j l
    exact (hn.2.1 y hy j l).le
  have hb : ∀ᶠ n in atTop, ∀ y ∈ good n,
      dist (x n * F.inclusionN (sampled n * secondRoot n y) * chart n (z₀ n))
        (x n * F.inclusionN (sampled n * vertex 0 n y (Fin.last (P 0).length)) *
          chart n (z₀ n)) ≤ Dbridge * scale n := by
    filter_upwards [hbridge, hz₀] with n hn hz y _hy
    have hzchart : chart n (z₀ n) = Exp (scale n •
        (pivot : GroupLieAlgebra (𝓘(ℝ, EG)) G)) := hz.1
    rw [hzchart]
    change dist (x n * F.inclusionN (sampled n * secondRoot n y) * _)
      (x n * F.inclusionN (sampled n *
        F.ExpN (F.N.equiv (D.vertex 0 n y (Fin.last (P 0).length)))) * _) ≤ _
    rw [hfirst n y]
    simpa only [map_mul, mul_assoc, dist_mul_left] using hn y
  exact MeasuredProbeRegions.offset_nonpos_of_linked_probe_bounds
    (N := F.N.carrier) (D := F.D.carrier) (G := G) (Q := QT) (W := W) (V := W)
    πT hπT μT μTI μ νD F.action F.inclusionN F.inclusionD F.conjugation hφ
    actionQ act hact scale hscale (fun n => lt_of_lt_of_le zero_lt_one (hscale1 n)) P₂ regions hμ
    πS hπS μQS μIS μS hφS σS hσS hμS flow hflow F.closedN hΛ p dseq
    ZQ J hZm hJm hZ0 hZt hJ0 hJt good (fun n => (hgood n).1) hmass P₁ hv hvol tiles tile
    π x sampled baseGroup (fun n => baseGroup n * step n) anchorRoot secondRoot
    (fun j => (P j).length) vertex hstart hthird hfirst hanchor hsecond
    chart q z₀ A bval hchart cell hcell hcell0 hcelltop hsmall F.surjective
    η ηnonneg hη δtarget Cp Dbridge
    (fun k => (fun z => A (z - eW (heightProjection T.character pivot))) '' Eprobe k)
    hδtarget (fun n => (p n).property.1.1) hDb hregions hbaseProfiles hprefix hb
    (by filter_upwards [hframes] with n hn; exact hn.2.2)
    ell tileLoss htileLoss htile0 hHaar htiles

end PolycyclicRecognition.CartanWordModel

end

end OAI
