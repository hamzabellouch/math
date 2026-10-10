import OAI.Analysis.TracialSplitting.FinitePacking

namespace OAI

universe uE uF uN uR


section

noncomputable section

namespace Pureness

namespace CStarAlgebraNorm

variable {R : Type uR} [Ring R] [StarRing R] [Algebra ℂ R]

def ofFaithful {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) : CStarAlgebraNorm R where
  toFun x := ‖f x‖
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using norm_add_le (f x) (f y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using norm_mul_le (f x) (f y)
  eq_zero_of_map_eq_zero' x hx := hf (by simpa using norm_eq_zero.mp hx)
  smul' c x := by simp [norm_smul]
  cstar x := by
    change ‖f (star x * x)‖ = ‖f x‖ * ‖f x‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]

@[simp] lemma ofFaithful_apply {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) (x : R) :
    (ofFaithful f hf).toAlgebraNorm x = ‖f x‖ := rfl

end CStarAlgebraNorm

open scoped TensorProduct

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

theorem IsNuclear.faithful_tensor_norm_eq (hA : IsNuclear.{u, v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ = ‖g z‖ := by
  have he := (hA B).elim (CStarAlgebraNorm.ofFaithful f hf)
    (CStarAlgebraNorm.ofFaithful g hg)
  exact congrArg (fun p : CStarAlgebraNorm (A ⊗[ℂ] B) => p.toAlgebraNorm z) he

theorem IsNuclear.tensor_norm_le_faithful (hA : IsNuclear.{u, v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ ≤ ‖g z‖ := by
  let fg := f.prod g
  have hfg : Function.Injective fg := by
    intro x y h
    exact hg (congrArg Prod.snd h)
  have he := hA.faithful_tensor_norm_eq fg g hfg hg z
  exact (norm_fst_le (fg z)).trans_eq he

end Pureness

end

end

end OAI
