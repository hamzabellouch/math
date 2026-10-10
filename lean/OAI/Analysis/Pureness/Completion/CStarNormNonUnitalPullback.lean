import OAI.Analysis.Pureness.Completion.CStarNormCompletion

namespace OAI
noncomputable section
namespace CuntzPureness.CStarAlgebraNorm
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

def ofFaithfulNonUnital {N : Type*} [NonUnitalCStarAlgebra N]
    (φ : R →⋆ₙₐ[ℂ] N) (hφ : Function.Injective φ) : CStarAlgebraNorm R where
  toFun x := ‖φ x‖
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using norm_add_le (φ x) (φ y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using norm_mul_le (φ x) (φ y)
  eq_zero_of_map_eq_zero' x hx := hφ (by simpa using norm_eq_zero.mp hx)
  smul' c x := by simp [norm_smul]
  cstar x := by
    change ‖φ (star x*x)‖=‖φ x‖*‖φ x‖
    rw [map_mul,map_star,CStarRing.norm_star_mul_self]

variable {S : Type*} [Ring S] [StarRing S] [Algebra ℂ S] [StarModule ℂ S]

def comapNonUnital (p : CStarAlgebraNorm S) (φ : R →⋆ₙₐ[ℂ] S)
    (hφ : Function.Injective φ) : CStarAlgebraNorm R :=
  ofFaithfulNonUnital (p.completionMap.comp φ) (p.completionMap_injective.comp hφ)

lemma comapNonUnital_apply (p : CStarAlgebraNorm S) (φ : R →⋆ₙₐ[ℂ] S)
    (hφ : Function.Injective φ) (x : R) :
    (p.comapNonUnital φ hφ).toAlgebraNorm x=p.toAlgebraNorm (φ x) :=
  p.completionMap_norm (φ x)
end CuntzPureness.CStarAlgebraNorm

end

end OAI
