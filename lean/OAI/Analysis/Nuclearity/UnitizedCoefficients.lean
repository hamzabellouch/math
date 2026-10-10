import OAI.Analysis.PureInfiniteness.RelativeCoefficientEnlargement

namespace OAI

/-! Finite output coefficients in the unitization. Products with elements of
the original algebra stay in that algebra. In particular, coefficients from
a unital cyclic representation do not require a unit in the original algebra. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [Fintype I]

lemma inr_fintype_sum (f : I → D) :
    ((∑ i, f i : D) : Unitization ℂ D) = ∑ i, (f i : Unitization ℂ D) :=
  map_sum (Unitization.inrNonUnitalAlgHom ℂ D) f Finset.univ

def unitizedRightMul (x : D) (a : Unitization ℂ D) : D := a.fst • x + x * a.snd

def unitizedLeftMul (a : Unitization ℂ D) (x : D) : D := a.fst • x + a.snd * x

lemma inr_unitizedRightMul (x : D) (a : Unitization ℂ D) :
    ((unitizedRightMul x a : D) : Unitization ℂ D) = (x : Unitization ℂ D) * a := by
  apply Unitization.ext <;> simp [unitizedRightMul]

lemma inr_unitizedLeftMul (a : Unitization ℂ D) (x : D) :
    ((unitizedLeftMul a x : D) : Unitization ℂ D) = a * (x : Unitization ℂ D) := by
  apply Unitization.ext <;> simp [unitizedLeftMul]

def unitizedSandwich (a : Unitization ℂ D) (x : D) (b : Unitization ℂ D) : D :=
  unitizedRightMul (unitizedLeftMul (star a) x) b

lemma inr_unitizedSandwich (a : Unitization ℂ D) (x : D) (b : Unitization ℂ D) :
    ((unitizedSandwich a x b : D) : Unitization ℂ D) =
      star a * (x : Unitization ℂ D) * b := by
  rw [unitizedSandwich, inr_unitizedRightMul, inr_unitizedLeftMul]

lemma unitizedSandwich_sub (a : Unitization ℂ D) (x y : D) (b : Unitization ℂ D) :
    unitizedSandwich a (x - y) b = unitizedSandwich a x b - unitizedSandwich a y b := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [inr_unitizedSandwich, Unitization.inr_sub, mul_sub, sub_mul]

lemma norm_unitizedSandwich_le (a : Unitization ℂ D) (x : D) (b : Unitization ℂ D) :
    ‖unitizedSandwich a x b‖ ≤ ‖a‖ * ‖x‖ * ‖b‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ), inr_unitizedSandwich]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (by simpa only [norm_star, Unitization.norm_inr] using
      norm_mul_le (star a) (x : Unitization ℂ D)) (norm_nonneg b))

def unitizedCoefficientEnlargement (T : B → D) (a : I → Unitization ℂ D)
    (c : I → B) (b : B) : D :=
  ∑ i, ∑ j, unitizedSandwich (a i) (T (star (c i) * b * c j)) (a j)

lemma inr_unitizedCoefficientEnlargement (T : B → D) (a : I → Unitization ℂ D)
    (c : I → B) (b : B) :
    ((unitizedCoefficientEnlargement T a c b : D) : Unitization ℂ D) =
      ∑ i, ∑ j, star (a i) * (T (star (c i) * b * c j) : Unitization ℂ D) * a j := by
  simp only [unitizedCoefficientEnlargement, inr_fintype_sum, inr_unitizedSandwich]

lemma unitizedCoefficientEnlargement_inner (φ : B →⋆ₙₐ[ℂ] D)
    (a : I → Unitization ℂ D) (c : I → B) (d : D) (b : B) :
    unitizedCoefficientEnlargement (innerHomCompression φ d) a c b =
      star (∑ i, unitizedRightMul (φ (c i) * d) (a i)) * φ b *
        (∑ i, unitizedRightMul (φ (c i) * d) (a i)) := by
  apply Unitization.inr_injective (R := ℂ)
  simp only [inr_unitizedCoefficientEnlargement, innerHomCompression_apply,
    map_mul, map_star, Unitization.inr_mul, Unitization.inr_star,
    inr_fintype_sum, inr_unitizedRightMul, star_sum, Finset.sum_mul,
    Finset.mul_sum, star_mul, mul_assoc]
  exact Finset.sum_comm

end WeakPureInfiniteness

end

end OAI
