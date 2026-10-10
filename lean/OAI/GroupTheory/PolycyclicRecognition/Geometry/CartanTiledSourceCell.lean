import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialQuotientSection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SectionProbeReparametrization
import OAI.GroupTheory.PolycyclicRecognition.Analysis.KernelHaarTransport

namespace OAI

/-! # The counted samplers on the original quotient/kernel probability cell -/

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

/-- The actual quotient chart associated to the section retained by the tiles. -/
def TiledProbeChainData.sourceQuotientCoordinates :
    (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) ≃ₜ Q.carrier :=
  (D.bQ.equivFun.symm.trans Q.equiv.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chartQ

/-- The tile construction's fixed linear section as a continuous group section. -/
def TiledProbeChainData.sourceSection : C(Q.carrier, F.N.carrier) :=
  exponentialQuotientSection (M.coneWordIdeal C) D.bQ D.lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The fixed section evaluated in the actual quotient chart. -/
theorem TiledProbeChainData.sourceSection_coordinates
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (z : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) :
    TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN) (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) z) =
      F.ExpN (F.N.equiv (quotientLinearSection (M.coneWordIdeal C) D.bQ D.lift
        (D.bQ.equivFun.symm z))) := by
  change exponentialQuotientSection (M.coneWordIdeal C) D.bQ D.lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ
    (chartQ (Q.equiv (D.bQ.equivFun.symm z))) = _
  exact (exponentialQuotientSection_apply (M.coneWordIdeal C) D.bQ D.lift
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ
    (D.bQ.equivFun.symm z)).trans (hchartN _)

/-- The fixed quotient part of the original source probability cell. -/
def TiledProbeChainData.sourceQuotientCell : Set Q.carrier :=
  (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale)
    (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D)
    (Q := Q) (chartQ := chartQ)) ''
      closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1

/-- The scale-dependent kernel part of the original source cell. -/
def TiledProbeChainData.sourceKernelCell (n : ℕ) : Set πQ.ker :=
  kernelRealization πQ ι hι hrange ''
    M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1

/-- The original quotient and kernel cell underlying the tile probes. -/
def TiledProbeChainData.sourceCell (n : ℕ) : Set (Q.carrier × πQ.ker) :=
  (TiledProbeChainData.sourceQuotientCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
    (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale)
    (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D)
    (Q := Q) (chartQ := chartQ)) ×ˢ
  (TiledProbeChainData.sourceKernelCell (T := T) (M := M) (F := F)
    (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI)
    (E := E) (β := β) (scale := scale) (ι := ι) (Q := Q)
    (πQ := πQ) (hι := hι) (hrange := hrange) n)

/-- Reparametrization uses the actual Haar product cell, so the selected
probability measure can be chosen there before concentration is applied. -/
def TiledProbeChainData.sourceCoordinates (n : ℕ) :=
  sectionProbeCoordinates
    (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ))
    (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1)

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- This section is a right inverse of the actual source quotient. -/
theorem TiledProbeChainData.sourceSection_rightInverse
    (hπ : ∀ v, πQ (chartN (F.N.equiv v)) =
      chartQ (Q.equiv ((M.coneWordIdeal C).toSubmodule.mkQ v))) :
    ∀ q, πQ (TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN) q) = q :=
  exponentialQuotientSection_rightInverse (M.coneWordIdeal C) D.bQ D.lift D.lifts
    F.N.equiv.toLinearEquiv Q.equiv.toLinearEquiv chartN chartQ πQ hπ

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- The first sampled endpoint is exactly kernel times the fixed section,
with no change to the original sampling measure or chosen starting point. -/
theorem TiledProbeChainData.source_first
    (hchartN : ∀ v, chartN v = F.ExpN v) (n : ℕ)
    (y : (TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n)) :
    D.probe n 0 (TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n y) =
        (y.val.2 : F.N.carrier) *
          TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN) y.val.1 := by
  rw [D.first]
  let eQ := TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ)
  let ψ := TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
  have hi := sectionProbeCoordinates_snd eQ (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1) y
  have hi' : ι (ψ y).2.val = (y.val.2 : F.N.carrier) := congrArg Subtype.val hi
  refine congrArg₂ (fun a b : F.N.carrier => a * b) hi' ?_
  have hq := sectionProbeCoordinates_fst eQ (kernelRealization πQ ι hι hrange).toHomeomorph
    (closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1)
    (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
      (β 0) (scale n) 1) y
  exact (TiledProbeChainData.sourceSection_coordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    hchartN (ψ y).1.val).symm.trans (congrArg
      (TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)) hq)

omit [IsTopologicalGroup I] in
/-- Every stored chain is retained on the original source probability cell. -/
theorem TiledProbeChainData.source_chains :
    let ψ := fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
    Nonempty (∀ j, M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
      (fun n y => D.probe n j (ψ n y))) := by
  dsimp only
  let : SecondCountableTopology Q.carrier :=
    (TiledProbeChainData.sourceQuotientCoordinates (T := T) (M := M) (F := F)
      (hunimod := hunimod) (eW := eW) (C := C) (ExpI := ExpI) (bN := bN)
      (E := E) (β := β) (ambient := ambient) (t := t) (scale := scale) (φ := φ)
      (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q)
      (chartQ := chartQ)).symm.secondCountableTopology
  let : SecondCountableTopology πQ.ker :=
    (kernelRealization πQ ι hι hrange).symm.toHomeomorph.secondCountableTopology
  let ψ := fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
  exact ⟨fun j => BoxProbeChains.reparametrize T M F hunimod eW bN (E j) ambient t scale
    (fun n => D.probe n j) (Classical.choice (D.chains j)) (fun n y => ψ n y)
    (fun n => (ψ n).continuous.measurable)⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
