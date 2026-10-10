import OAI.Analysis.KadisonKastler.HilbertMatrix
import OAI.Analysis.KadisonKastler.CompletelyPositive
import Mathlib.Analysis.InnerProductSpace.StarOrder

namespace OAI

/-! # Complete positivity of compression between two Hilbert spaces -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance compressionOperatorOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : PartialOrder (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrder _
local instance compressionOperatorStarOrder {J : Type*} [NormedAddCommGroup J]
    [InnerProductSpace ℂ J] [CompleteSpace J] : StarOrderedRing (J →L[ℂ] J) :=
  CStarAlgebra.spectralOrderedRing _

/-- Applying a continuous linear map in each coordinate of a finite Hilbert sum. -/
def finiteDiagonalMap (V : H →L[ℂ] K) (n : ℕ) :
    Generator.FiniteHilbert (Fin n) H →L[ℂ] Generator.FiniteHilbert (Fin n) K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => V.comp (PiLp.proj 2 (fun _ : Fin n => H) i)))

omit [CompleteSpace H] [CompleteSpace K] in
@[simp]
theorem finiteDiagonalMap_apply (V : H →L[ℂ] K) (n : ℕ)
    (x : Generator.FiniteHilbert (Fin n) H) (i : Fin n) :
    finiteDiagonalMap V n x i = V (x i) := rfl

theorem finiteDiagonalMap_adjoint (V : H →L[ℂ] K) (n : ℕ) :
    (finiteDiagonalMap V n).adjoint = finiteDiagonalMap V.adjoint n := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [PiLp.inner_apply, finiteDiagonalMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact ContinuousLinearMap.adjoint_inner_left V (y i) (x i)

/-- Compression by a bounded operator between two different Hilbert spaces. -/
def hilbertCompression (V : H →L[ℂ] K) : (K →L[ℂ] K) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun T := V.adjoint ∘L T ∘L V
  map_add' S T := by ext x; simp
  map_smul' c T := by ext x; simp

/-- Compression is completely positive at every finite matrix size. -/
def hilbertCompressionCP (V : H →L[ℂ] K) : (K →L[ℂ] K) →CP (H →L[ℂ] H) where
  toLinearMap := hilbertCompression V
  map_cstarMatrix_nonneg' n X hX := by
    have hpos : 0 ≤ hilbertMatrix X := map_nonneg (hilbertMatrixHom (H := K)) hX
    let W := finiteDiagonalMap V n
    have hp : 0 ≤ hilbertCompression W (hilbertMatrix X) := by
      rw [StarOrderedRing.nonneg_iff] at hpos
      refine AddSubmonoid.closure_induction (fun T hT => ?_) (by simp [hilbertCompression])
        (fun T U _ _ hT hU => ?_) hpos
      · obtain ⟨S, rfl⟩ := hT
        have he : hilbertCompression W (star S * S) = (S ∘L W).adjoint ∘L (S ∘L W) := by
          simp only [hilbertCompression, LinearMap.coe_mk, AddHom.coe_mk,
            ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
          rfl
        rw [he]
        have hpositive := ContinuousLinearMap.isPositive_adjoint_comp_self (S ∘L W)
        change IsSelfAdjoint (_ - 0) ∧ QuasispectrumRestricts (_ - 0) _
        simp only [sub_zero]
        exact ⟨hpositive.isSelfAdjoint,
          quasispectrumRestricts_iff_spectrumRestricts.mpr hpositive.spectrumRestricts⟩
      · exact (map_add (hilbertCompression W) T U).symm ▸ add_nonneg hT hU
    have he : hilbertMatrix (CStarMatrix.mapₗ (hilbertCompression V) X) =
        (finiteDiagonalMap V n).adjoint ∘L hilbertMatrix X ∘L finiteDiagonalMap V n := by
      rw [finiteDiagonalMap_adjoint]
      apply ContinuousLinearMap.ext
      intro x
      apply PiLp.ext
      intro i
      simp only [hilbertMatrix_apply, ContinuousLinearMap.comp_apply, finiteDiagonalMap_apply,
        map_sum]
      rfl
    have hleft : 0 ≤ hilbertMatrix (CStarMatrix.mapₗ (hilbertCompression V) X) := by
      rw [he]
      exact hp
    have hr := (NonUnitalStarAlgHom.map_le_map_iff (hilbertMatrixHom (H := H))
      hilbertMatrixHom_injective (x := 0)
      (y := CStarMatrix.mapₗ (hilbertCompression V) X)).mp
    apply hr
    rw [map_zero]
    change 0 ≤ hilbertMatrix (CStarMatrix.mapₗ (hilbertCompression V) X)
    exact hleft

end

end KadisonKastler

end OAI
