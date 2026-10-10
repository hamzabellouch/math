import Mathlib

namespace OAI

noncomputable section

namespace KKConcreteCorner

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (S : Submodule ℂ H) [CompleteSpace S]

def compress (x : H →L[ℂ] H) : S →L[ℂ] S :=
  S.orthogonalProjectionOnto ∘L x ∘L S.subtypeL

def extend (x : S →L[ℂ] S) : H →L[ℂ] H :=
  S.subtypeL ∘L x ∘L S.orthogonalProjectionOnto

@[simp] theorem compress_extend (x : S →L[ℂ] S) : compress S (extend S x)=x := by
  ext v
  simp [compress,extend]

@[simp] theorem extend_compress (x : H →L[ℂ] H) :
    extend S (compress S x)=S.starProjection*x*S.starProjection := by
  rfl

@[simp] theorem extend_zero : extend S 0=0 := by simp [extend]

@[simp] theorem extend_one : extend S 1=S.starProjection := by ext v; rfl

@[simp] theorem extend_add (x y : S →L[ℂ] S) : extend S (x+y)=extend S x+extend S y := by
  simp [extend,ContinuousLinearMap.add_comp,ContinuousLinearMap.comp_add]

@[simp] theorem extend_smul (c : ℂ) (x : S →L[ℂ] S) : extend S (c • x)=c • extend S x := by
  simp [extend]

@[simp] theorem extend_mul (x y : S →L[ℂ] S) : extend S (x*y)=extend S x*extend S y := by
  ext v
  simp [extend]

@[simp] theorem extend_star [CompleteSpace H] (x : S →L[ℂ] S) : extend S (star x)=star (extend S x) := by
  simp only [extend,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL,Submodule.adjoint_orthogonalProjectionOnto,ContinuousLinearMap.comp_assoc]

theorem extend_injective : Function.Injective (extend S) := by
  intro x y h
  simpa only [compress_extend] using congrArg (compress S) h

theorem extend_supported (x : S →L[ℂ] S) :
    S.starProjection*extend S x=extend S x ∧ extend S x*S.starProjection=extend S x := by
  constructor
  · rw [← extend_one,← extend_mul,one_mul]
  · rw [← extend_one,← extend_mul,mul_one]

@[simp] theorem compress_star [CompleteSpace H] (x : H →L[ℂ] H) : compress S (star x)=star (compress S x) := by
  simp only [compress,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL,Submodule.adjoint_orthogonalProjectionOnto,ContinuousLinearMap.comp_assoc]

theorem projection_isStar [CompleteSpace H] : IsStarProjection S.starProjection :=
  isStarProjection_starProjection

theorem extend_norm_le (x : S →L[ℂ] S) : ‖extend S x‖ ≤ ‖x‖ := by
  apply (extend S x).opNorm_le_bound (norm_nonneg x)
  intro v
  change ‖(x (S.orthogonalProjectionOnto v) : H)‖ ≤ ‖x‖*‖v‖
  change ‖x (S.orthogonalProjectionOnto v)‖ ≤ _
  exact (x.le_opNorm _).trans (mul_le_mul_of_nonneg_left (S.norm_orthogonalProjectionOnto_apply_le v) (norm_nonneg _))

end

end KKConcreteCorner
end

end OAI
