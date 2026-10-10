import OAI.NumberTheory.Ostmann.Characters.GaussFourthMoment

namespace OAI

/-!
# Summing the nonprincipal fourth moment over bottom-pair characters

Only the common mass bound, the maximum squared mass, and the total
squared mass of the nonnegative Fourier weights enter this calculation.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance fourthFamilyFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance fourthFamilyDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem nonprincipal_fourth_family_bound {p : ℕ} [Fact p.Prime]
    (f : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (w : MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (hf : ∀ χ a, additiveFourier (f χ) a = (w χ a : ℂ))
    (hw : ∀ χ a, 0 ≤ w χ a)
    (J R S : ℝ) (hR : 0 ≤ R)
    (hmass : ∀ χ, (∑ a : ZMod p, w χ a) ≤ J)
    (hmax : ∀ χ, (∑ a : ZMod p, w χ a ^ 2) ≤ R)
    (htotal : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2) ≤ S) :
    (∑ χ : MulChar (ZMod p) ℂ,
      ∑ α ∈ (Finset.univ : Finset (MulChar (ZMod p) ℂ)).erase 1,
        ∑ a : ZMod p, ‖additiveFourier (fun x => f χ x * α x) a‖ ^ 4) ≤
      2 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ)) * R * S +
        3 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2) * J ^ 4 := by
  classical
  let r : MulChar (ZMod p) ℂ → ℝ := fun χ => ∑ a : ZMod p, w χ a ^ 2
  have hr (χ : MulChar (ZMod p) ℂ) : 0 ≤ r χ :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hrs : (∑ χ : MulChar (ZMod p) ℂ, r χ ^ 2) ≤ R * S := by
    calc
      _ ≤ ∑ χ : MulChar (ZMod p) ℂ, R * r χ := by
        apply Finset.sum_le_sum
        intro χ _
        have hm : r χ ≤ R := hmax χ
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hm (hr χ)
      _ = R * ∑ χ : MulChar (ZMod p) ℂ, r χ := (Finset.mul_sum _ _ _).symm
      _ ≤ R * S := mul_le_mul_of_nonneg_left htotal hR
  have hm (χ : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, w χ a) ^ 4 ≤ J ^ 4 :=
    pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => hw χ a)) (hmass χ) 4
  have hms : (∑ χ : MulChar (ZMod p) ℂ, (∑ a : ZMod p, w χ a) ^ 4) ≤
      (Fintype.card (ZMod p)ˣ : ℝ) * J ^ 4 := by
    calc
      _ ≤ ∑ _χ : MulChar (ZMod p) ℂ, J ^ 4 := Finset.sum_le_sum (fun χ _ => hm χ)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        card_mulChar_eq_card_units]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  calc
    _ ≤ ∑ χ : MulChar (ZMod p) ℂ,
        ((p : ℝ)⁻¹) ^ 2 *
          (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) * r χ ^ 2 +
            3 * (∑ a : ZMod p, w χ a) ^ 4) := by
      exact Finset.sum_le_sum fun χ _ => nonprincipal_fourier_fourth_bound (f χ) (w χ) (hf χ) (hw χ)
    _ = ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) *
          (∑ χ : MulChar (ZMod p) ℂ, r χ ^ 2) +
          3 * (∑ χ : MulChar (ZMod p) ℂ, (∑ a : ZMod p, w χ a) ^ 4)) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((p : ℝ)⁻¹) ^ 2 *
        (2 * (p : ℝ) * (Fintype.card (ZMod p)ˣ : ℝ) * (R * S) +
          3 * ((Fintype.card (ZMod p)ˣ : ℝ) * J ^ 4)) := by
      gcongr
    _ = _ := by field_simp

end Ostmann

end OAI
