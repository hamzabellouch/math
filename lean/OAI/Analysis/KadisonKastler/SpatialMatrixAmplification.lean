import OAI.Analysis.KadisonKastler.SpatialMatrixDensity
import OAI.Analysis.KadisonKastler.CompletelyPositive
import OAI.Analysis.KadisonKastler.MatrixOperatorGeneration

namespace OAI

/-! # Finite matrix amplification of spatial matrix images

Finite matrices over a generated operator algebra generate the matrix
von Neumann algebra.  The proof uses the existing strong approximation
theorem entry by entry.  Flattening the two finite matrix indices then
preserves the complete unit-ball approximation constant.
-/

namespace KadisonKastler

open UnitalTomsWinter Generator Filter
open scoped Topology BigOperators

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance spatialAmplificationOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance spatialAmplificationStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance spatialAmplificationTargetOrder :
    PartialOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrder (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
local instance spatialAmplificationTargetStarOrder :
    StarOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  CStarAlgebra.spectralOrderedRing (SpatialHilbert H K →L[ℂ] SpatialHilbert H K)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Entrywise amplification of the finite spatial matrix representation. -/
def spatialMatrixAmplification (E : MatrixUnitSystem κ (K →L[ℂ] K)) :
    CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)) →⋆ₐ[ℂ]
      CStarMatrix ι ι (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  coefficientMatrixMap (n := ι) (A := CStarMatrix κ κ (H →L[ℂ] H))
    (B := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialMatrixHom (H := H) E)

@[simp]
theorem spatialMatrixAmplification_apply (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H))) (i j : ι) :
    spatialMatrixAmplification E X i j = spatialMatrixHom E (X i j) := rfl

theorem spatialMatrixAmplification_injective [Nonempty κ] [Nontrivial K]
    (E : MatrixUnitSystem κ (K →L[ℂ] K)) :
    Function.Injective (spatialMatrixAmplification (H := H) (ι := ι) E) := by
  intro X Y hXY
  apply CStarMatrix.ext
  intro i j
  apply spatialMatrixHom_injective E
  exact congrArg (fun Z => Z i j) hXY

theorem norm_spatialMatrixAmplification [Nonempty κ] [Nontrivial K]
    (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H))) :
    ‖spatialMatrixAmplification E X‖ = ‖X‖ :=
  NonUnitalStarAlgHom.norm_map (spatialMatrixAmplification E)
    (spatialMatrixAmplification_injective E) X

/-- Flattening lets the original complete approximation hypothesis control
every finite amplification of a spatial matrix image. -/
theorem MatrixNearInclusion.spatialMatrixAmplification_approx
    {M N : VonNeumannAlgebra H} {γ : ℝ} (h : MatrixNearInclusion M N γ)
    [Nonempty κ] [Nontrivial K] (E : MatrixUnitSystem κ (K →L[ℂ] K))
    (X : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)))
    (hX : ∀ i j a b, X i j a b ∈ M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H)),
      (∀ i j a b, Y i j a b ∈ N) ∧ ‖Y‖ ≤ 1 ∧
      ‖spatialMatrixAmplification E X - spatialMatrixAmplification E Y‖ ≤ γ := by
  let e := cstarMatrixComp (A := H →L[ℂ] H) ι κ
  have he (Z : CStarMatrix ι ι (CStarMatrix κ κ (H →L[ℂ] H))) : ‖e Z‖ = ‖Z‖ :=
    NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective Z
  have hes (Z : CStarMatrix (ι × κ) (ι × κ) (H →L[ℂ] H)) : ‖e.symm Z‖ = ‖Z‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective Z
  obtain ⟨Y, hY, hYn, hc⟩ := h.square (e X)
    (fun i j => hX i.1 j.1 i.2 j.2) ((he X).le.trans hn)
  refine ⟨e.symm Y, (fun i j a b => hY (i, a) (j, b)), (hes Y).le.trans hYn, ?_⟩
  rw [← map_sub, norm_spatialMatrixAmplification]
  have hx : X = e.symm (e X) := (e.symm_apply_apply X).symm
  rw [hx, ← map_sub, hes]
  exact hc

end

end KadisonKastler

end OAI
