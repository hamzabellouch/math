import OAI.Analysis.KadisonKastler.CenteredLabels
import OAI.Analysis.KadisonKastler.RectangularOperator

namespace OAI

/-! # The creation row from its covariance matrix -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance creationOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance creationOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance creationScalarOrder : PartialOrder ℂ := CStarAlgebra.spectralOrder _
local instance creationScalarStarOrder : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing _

/-- Scalars acting on a projection corner form a nonunital star representation. -/
def scalarProjectionHom (P : H →L[ℂ] H) (hP : IsStarProjection P) :
    ℂ →⋆ₙₐ[ℂ] (H →L[ℂ] H) where
  toFun z := z • P
  map_zero' := zero_smul _ _
  map_add' z w := add_smul z w P
  map_smul' z w := mul_smul z w P
  map_mul' z w := by
    rw [smul_mul_assoc, mul_smul_comm, hP.isIdempotentElem.eq, smul_smul]
  map_star' z := by rw [star_smul, hP.isSelfAdjoint.star_eq]

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

def centeredCovariance : CStarMatrix α α ℂ :=
  (Fintype.card α : ℂ)⁻¹ • centeredLabelProjection

theorem norm_centeredCovariance_le :
    ‖centeredCovariance (α := α)‖ ≤ (Fintype.card α : ℝ)⁻¹ := by
  rw [centeredCovariance, norm_smul, norm_inv]
  have hn : ‖(Fintype.card α : ℂ)‖ = (Fintype.card α : ℝ) := by simp
  rw [hn]
  calc
    _ ≤ (Fintype.card α : ℝ)⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left
        (IsStarProjection.norm_le _ centeredLabelProjection_isStarProjection) (by positivity)
    _ = _ := mul_one _

/-- An operator row whose Gram matrix is the centered covariance has the
required dimension decay, even with an arbitrary Hilbert tail projection. -/
theorem norm_creationRow_le (C : α → H →L[ℂ] H) (P : H →L[ℂ] H)
    (hP : IsStarProjection P)
    (hGram : ∀ a b, star (C a) * C b =
      ((Fintype.card α : ℂ)⁻¹ *
        ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹)) • P) :
    ‖(CStarMatrix.ofMatrix (fun (_ : Unit) a => C a))‖ ≤
      (Real.sqrt (Fintype.card α : ℝ))⁻¹ := by
  let R : CStarMatrix Unit α (H →L[ℂ] H) := CStarMatrix.ofMatrix (fun _ a => C a)
  let φ := CStarMatrix.mapₙₐ (n := α) (scalarProjectionHom P hP)
  have he : R.conjTranspose * R = φ (centeredCovariance (α := α)) := by
    apply CStarMatrix.ext
    intro a b
    change (∑ _ : Unit, star (C a) * C b) =
      ((Fintype.card α : ℂ)⁻¹ *
        ((if a = b then 1 else 0) - (Fintype.card α : ℂ)⁻¹)) • P
    simpa only [Fintype.sum_unique] using hGram a b
  have hnorm : ‖R.conjTranspose * R‖ = ‖R‖ ^ 2 := by
    have heq : R.conjTranspose.conjTranspose = R := by
      apply CStarMatrix.ext
      intro i a
      simp only [CStarMatrix.conjTranspose_apply, star_star]
    have h := norm_rectangular_mul_star R.conjTranspose
    rw [heq, norm_rectangular_star] at h
    exact h
  have hb : ‖R‖ ^ 2 ≤ (Fintype.card α : ℝ)⁻¹ := by
    rw [← hnorm, he]
    exact (NonUnitalStarAlgHom.norm_apply_le φ _).trans norm_centeredCovariance_le
  change ‖R‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [inv_pow, Real.sq_sqrt (by positivity)]
  exact hb

end

end KadisonKastler

end OAI
