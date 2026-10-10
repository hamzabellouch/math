import OAI.NumberTheory.Jacobsthal.Probability.KloostermanFourthMoment

namespace OAI

namespace Erdos970

section

open scoped BigOperators ComplexConjugate

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

variable {F : Type*} [Field F] [Fintype F]

private theorem fourth_product_eq_norm (z : ℂ) :
    z*z*conj z*conj z = ((‖z‖^4 : ℝ) : ℂ) := by
  calc
    _ = (z * conj z)^2 := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
      congr 1
      ring

theorem fourth_norm_identity (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) :
    (∑ a : F, ∑ b : F, ‖sum ψ a b‖^4) =
      (Fintype.card F : ℝ)^2 * (pairCollisions F).card := by
  have h := fourth_moment_identity ψ hψ
  simp_rw [fourth_product_eq_norm] at h
  exact_mod_cast h

private theorem unit_orbit_bound (ψ : AddChar F ℂ) (a b : F) (ha : a ≠ 0) :
    (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 ≤
      ∑ x : F × F, ‖sum ψ x.1 x.2‖^4 := by
  let f : Fˣ → F × F := fun c => (a * (c : F), b * (↑c⁻¹ : F))
  have hf : Function.Injective f := by
    intro c d h
    apply Units.ext
    exact mul_left_cancel₀ ha (congrArg Prod.fst h)
  have heq : (∑ x ∈ Finset.univ.image f, ‖sum ψ x.1 x.2‖^4) =
      (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 := by
    rw [Finset.sum_image]
    · simp only [f, sum_unit_scale, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    · exact fun c _ d _ h => hf h
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)

theorem fourth_norm_le (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (a b : F) (hab : a ≠ 0 ∨ b ≠ 0) :
    ‖sum ψ a b‖^4 ≤ 3 * (Fintype.card F : ℝ)^3 := by
  have left (a b : F) (ha : a ≠ 0) :
      ‖sum ψ a b‖^4 ≤ 3 * (Fintype.card F : ℝ)^3 := by
    have horbit := unit_orbit_bound ψ a b ha
    rw [Fintype.sum_prod_type, fourth_norm_identity ψ hψ] at horbit
    have hc : ((pairCollisions F).card : ℝ) ≤ 3 * (Fintype.card Fˣ : ℝ)^2 := by
      exact_mod_cast pairCollisions_card_le F
    have hu : (0 : ℝ) < Fintype.card Fˣ := by exact_mod_cast Fintype.card_pos
    have hf : (Fintype.card Fˣ : ℝ) ≤ (Fintype.card F : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective (fun x : Fˣ => (x : F)) Units.val_injective
    have hbound : (Fintype.card Fˣ : ℝ) * ‖sum ψ a b‖^4 ≤
        (Fintype.card Fˣ : ℝ) * (3 * (Fintype.card F : ℝ)^2 * Fintype.card Fˣ) := by
      calc
        _ ≤ (Fintype.card F : ℝ)^2 * (pairCollisions F).card := horbit
        _ ≤ (Fintype.card F : ℝ)^2 * (3 * (Fintype.card Fˣ : ℝ)^2) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg _)
        _ = _ := by ring
    have hcancel := (mul_le_mul_iff_right₀ hu).mp hbound
    calc
      _ ≤ 3 * (Fintype.card F : ℝ)^2 * Fintype.card Fˣ := hcancel
      _ ≤ 3 * (Fintype.card F : ℝ)^2 * Fintype.card F :=
        mul_le_mul_of_nonneg_left hf (by positivity)
      _ = _ := by ring
  rcases hab with ha | hb
  · exact left a b ha
  · rw [sum_swap]
    exact left b a hb

end ErdosKloosterman

end

end Erdos970

end OAI
