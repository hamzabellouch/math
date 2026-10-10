import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceCell
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledLinkedEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The fixed section in the actual source-cell coordinates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

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


local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The quotient coordinate used by the compact source cell evaluates the
same fixed pure-word section used by the metric bridge. -/
theorem TiledProbeChainData.sourceSection_sourceCoordinates
    (hchartN : ∀ v, chartN v = F.ExpN v) (n : ℕ) (y : Y n) :
    σ y.val.1 = F.ExpN (F.N.equiv
      (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift
        (D.bQ.equivFun.symm (ψ n y).1.val))) := by
  have hsection := TiledProbeChainData.sourceSection_coordinates
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
    (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN) hchartN (ψ n y).1.val
  let eQ := TiledProbeChainData.sourceQuotientCoordinates
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
    (D := D) (Q := Q) (chartQ := chartQ)
  have hq' : eQ (ψ n y).1.val = y.val.1 := eQ.apply_symm_apply _
  exact (congrArg σ hq').symm.trans hsection

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- Retaining the linear section before selecting the tiling keeps the
contact-bridge constants independent of that later selection. -/
theorem TiledProbeChainData.sourceSection_eq_fixed_coordinates
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (τ : (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ)
      →ₗ[ℝ] cartanRootIdeal H)
    (hτ : (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift).comp
      D.bQ.equivFun.symm.toLinearMap = τ)
    (n : ℕ) (y : Y n) :
    σ y.val.1 = F.ExpN (F.N.equiv (τ (ψ n y).1.val)) := by
  have hs := TiledProbeChainData.sourceSection_sourceCoordinates
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
    (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    (πQ := πQ) (hι := hι) (hrange := hrange) hchartN n y
  have he := congrArg (fun f => f (ψ n y).1.val) hτ
  exact hs.trans (congrArg (fun v => F.ExpN (F.N.equiv v)) he)

end PolycyclicRecognition.CartanWordModel

end

end OAI
