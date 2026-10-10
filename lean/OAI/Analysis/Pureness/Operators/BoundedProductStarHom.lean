import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.lpSpace

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ENNReal
variable {A E : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra E]

def boundedProductStarHom (φ : ℕ → A →⋆ₙₐ[ℂ] E) :
    A →⋆ₙₐ[ℂ] lp (fun _ : ℕ => E) ∞ where
  toFun x := ⟨fun n => φ n x, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n, rfl⟩
    exact NonUnitalStarAlgHom.norm_apply_le (φ n) x⟩⟩
  map_zero' := by apply lp.ext; funext n; exact _root_.map_zero (φ n)
  map_add' x y := by apply lp.ext; funext n; exact _root_.map_add (φ n) x y
  map_mul' x y := by apply lp.ext; funext n; exact _root_.map_mul (φ n) x y
  map_smul' c x := by apply lp.ext; funext n; exact _root_.map_smul (φ n) c x
  map_star' x := by apply lp.ext; funext n; exact (φ n).map_star' x

lemma boundedProductStarHom_apply (φ : ℕ → A →⋆ₙₐ[ℂ] E) (x : A) (n : ℕ) :
    boundedProductStarHom φ x n = φ n x := rfl

lemma boundedProductStarHom_norm_le (φ : ℕ → A →⋆ₙₐ[ℂ] E) (x : A) :
    ‖boundedProductStarHom φ x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (boundedProductStarHom φ) x
end CuntzPureness

end

end OAI
