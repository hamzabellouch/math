import Mathlib.SetTheory.Cardinal.Finite
import OAI.NumberTheory.Ostmann.Construction.RepeatedPrior
import OAI.NumberTheory.Ostmann.Tree.PartitionProducts

namespace OAI

/-! # Simultaneous prior domination for a fixed internal-prime equality pattern -/

namespace Ostmann
open scoped Classical BigOperators

private theorem product_pattern_fibers {I C : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (f : I → ℝ) :
    (∏ c, ∏ i : {i : I // pattern i = c}, f i.val) = ∏ i, f i := by
  exact Fintype.prod_fiberwise pattern f

private theorem product_pattern_powers {I C : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c}) (E : ℝ) :
    (∏ c, E ^ (Fintype.card {i : I // pattern i = c} - 1)) =
      E ^ (Fintype.card I - Fintype.card C) := by
  rw [Finset.prod_pow_eq_pow_sum, Finset.sum_tsub_distrib]
  · simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    congr 2
    simpa only [Fintype.card_eq_nat_card] using sum_card_partition pattern
  · intro c _
    exact Fintype.card_pos_iff.mpr ⟨rep c⟩

theorem repeated_pattern_prior_domination {I C A : Type*} [Fintype I] [Fintype C]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (value : A → ℝ) (E : ℝ)
    (hvalue : ∀ a, 2 ≤ value a)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, value a * μ i a ≤ E)
    (x : C → A) :
    ((∏ i, value (x (pattern i)) * μ i (x (pattern i))) *
        ∏ c, (value (x c) - 1)⁻¹) ≤
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
  have hl (c : C) :
      (∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) /
          (value (x c) - 1) ≤
        2 * μ (rep c).val (x c) * E ^ (Fintype.card {i : I // pattern i = c} - 1) := by
    simpa only [Finset.mem_univ, Finset.card_univ] using
      repeated_prior_weight_le (Finset.univ : Finset {i : I // pattern i = c}) (rep c)
        (Finset.mem_univ _) (fun i => μ i.val (x c)) (value (x c)) E (hvalue _)
        (fun i _ => hμ i.val _) (fun i _ => hbound i.val _)
  have hp := Finset.prod_le_prod₀ (s := (Finset.univ : Finset C))
    (fun c _ => div_nonneg
      (Finset.prod_nonneg (fun i _ => mul_nonneg (by linarith [hvalue (x c)]) (hμ i.val _)))
      (by linarith [hvalue (x c)])) (fun c _ => hl c)
  have hflat : (∏ c, ∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) =
      ∏ i, value (x (pattern i)) * μ i (x (pattern i)) := by
    calc
      _ = ∏ c, ∏ i : {i : I // pattern i = c},
          value (x (pattern i.val)) * μ i.val (x (pattern i.val)) := by
        apply Finset.prod_congr rfl
        intro c _
        apply Finset.prod_congr rfl
        intro i _
        rw [i.property]
      _ = _ := product_pattern_fibers pattern (fun i => value (x (pattern i)) * μ i (x (pattern i)))
  have hc := product_pattern_powers pattern rep E
  have hleft :
      (∏ c, (∏ i : {i : I // pattern i = c}, value (x c) * μ i.val (x c)) /
        (value (x c) - 1)) =
      (∏ i, value (x (pattern i)) * μ i (x (pattern i))) *
        ∏ c, (value (x c) - 1)⁻¹ := by
    simp only [div_eq_mul_inv]
    rw [Finset.prod_mul_distrib, hflat]
  have hright :
      (∏ c, 2 * μ (rep c).val (x c) * E ^ (Fintype.card {i : I // pattern i = c} - 1)) =
      ((2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)) *
        ∏ c, μ (rep c).val (x c) := by
    simp only [Finset.prod_mul_distrib, hc, Finset.prod_const, Finset.card_univ]
    ring
  rw [hleft, hright] at hp
  exact hp

theorem repeated_pattern_prior_mass_le {I C A : Type*} [Fintype I] [Fintype C] [Fintype A]
    (pattern : I → C) (rep : ∀ c, {i : I // pattern i = c})
    (μ : I → A → ℝ) (value : A → ℝ) (E : ℝ)
    (hE : 0 ≤ E) (hvalue : ∀ a, 2 ≤ value a)
    (hμ : ∀ i a, 0 ≤ μ i a) (hbound : ∀ i a, value a * μ i a ≤ E)
    (hmass : ∀ c, ∑ a, μ (rep c).val a ≤ 1) :
    (∑ x : C → A, (∏ i, value (x (pattern i)) * μ i (x (pattern i))) *
      ∏ c, (value (x c) - 1)⁻¹) ≤
      (2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C) := by
  let K := (2 : ℝ) ^ Fintype.card C * E ^ (Fintype.card I - Fintype.card C)
  have hK : 0 ≤ K := mul_nonneg (by positivity) (pow_nonneg hE _)
  calc
    _ ≤ ∑ x : C → A, K * ∏ c, μ (rep c).val (x c) :=
      Finset.sum_le_sum (fun x _ => repeated_pattern_prior_domination pattern rep μ value E hvalue hμ hbound x)
    _ = K * ∏ c, ∑ a, μ (rep c).val a := by rw [← Finset.mul_sum, Fintype.prod_sum]
    _ ≤ K * 1 := mul_le_mul_of_nonneg_left
      (Finset.prod_le_one₀ (fun c _ => Finset.sum_nonneg (fun a _ => hμ _ _))
        (fun c _ => hmass c)) hK
    _ = _ := mul_one K

end Ostmann

end OAI
