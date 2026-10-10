import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace OAI

/-!
# Degree control for products of prime centers

The argument is uniform in the indicators, so it applies both to integer
residues and to independent product residues. One prime is chosen from each
family, and the total number of lit prime coordinates controls the sum of
squared tuple weights.
-/

namespace TwoPointCorrelations

open Finset

lemma nonneg_product_le_power_card {ι : Type*} [Fintype ι]
    (b : ι → ℝ) (C : ℝ) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, b i ≤ C * Fintype.card ι) :
    ∏ i, b i ≤ C ^ Fintype.card ι := by
  classical
  by_cases hn : Fintype.card ι = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn
    simp
  have hp : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmean := Real.geom_mean_le_arith_mean (univ : Finset ι) (fun _ => (1 : ℝ)) b
    (fun _ _ => zero_le_one) (by simpa using hp) (fun i _ => hb i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at hmean
  have hbound : (∏ i, b i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ C :=
    hmean.trans ((div_le_iff₀ hp).mpr hsum)
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg (fun i _ => hb i)) _) hbound
    (Fintype.card ι)
  rw [Real.rpow_inv_natCast_pow (prod_nonneg (fun i _ => hb i)) hn] at hpow
  exact hpow

noncomputable def centerMagnitude (θ : ℝ) (lit : Bool) : ℝ :=
  |(if lit then 1 else 0) - θ|

lemma centerMagnitude_nonneg (θ : ℝ) (lit : Bool) : 0 ≤ centerMagnitude θ lit :=
  abs_nonneg _

lemma centerMagnitude_le_one (θ : ℝ) (lit : Bool) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    centerMagnitude θ lit ≤ 1 := by
  cases lit <;> simp [centerMagnitude, abs_of_nonneg, abs_of_nonpos, hθ, sub_nonneg.mpr hθ1]
  all_goals linarith

lemma centerMagnitude_le_indicator_add (θ : ℝ) (lit : Bool) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    centerMagnitude θ lit ≤ (if lit then 1 else 0) + θ := by
  cases lit <;> simp [centerMagnitude, abs_of_nonneg, abs_of_nonpos, hθ, sub_nonneg.mpr hθ1]
  all_goals linarith

lemma center_family_sum_le {α : Type*} [Fintype α]
    (θ : α → ℝ) (lit : α → Bool) (hθ : ∀ p, 0 ≤ θ p) (hθ1 : ∀ p, θ p ≤ 1) :
    (∑ p, centerMagnitude (θ p) (lit p)) ≤
      (∑ p, if lit p then (1 : ℝ) else 0) + ∑ p, θ p := by
  rw [← sum_add_distrib]
  exact sum_le_sum (fun p _ => centerMagnitude_le_indicator_add _ _ (hθ p) (hθ1 p))

lemma squared_center_products_le_product
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)]
    (θ : (i : ι) → P i → ℝ) (lit : (i : ι) → P i → Bool)
    (hθ : ∀ i p, 0 ≤ θ i p) (hθ1 : ∀ i p, θ i p ≤ 1) :
    (∑ x : (i : ι) → P i, (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ^ 2) ≤
      ∏ i, ((∑ p : P i, if lit i p then (1 : ℝ) else 0) + ∑ p, θ i p) := by
  classical
  calc
    _ ≤ ∑ x : (i : ι) → P i, ∏ i, centerMagnitude (θ i (x i)) (lit i (x i)) := by
      apply sum_le_sum
      intro x _
      have h0 : 0 ≤ ∏ i, centerMagnitude (θ i (x i)) (lit i (x i)) :=
        prod_nonneg (fun i _ => centerMagnitude_nonneg _ _)
      have h1 : (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ≤ 1 :=
        prod_le_one₀ (fun i _ => centerMagnitude_nonneg _ _) (fun i _ =>
          centerMagnitude_le_one _ _ (hθ i _) (hθ1 i _))
      simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left h1 h0
    _ = ∏ i, ∑ p, centerMagnitude (θ i p) (lit i p) :=
      (Fintype.prod_sum (fun i p => centerMagnitude (θ i p) (lit i p))).symm
    _ ≤ _ := by
      apply prod_le_prod₀
      · intro i _
        exact sum_nonneg (fun p _ => centerMagnitude_nonneg _ _)
      · intro i _
        exact center_family_sum_le (θ i) (lit i) (hθ i) (hθ1 i)

lemma sum_degree_budget {ι : Type*} [Fintype ι] (ω V : ι → ℝ) (W : ℝ)
    (hV : ∀ i, V i ≤ 2 * W)
    (hdegree : ∑ i, ω i ≤ 6 * W * Fintype.card ι) :
    ∑ i, (ω i + V i) ≤ (8 * W) * Fintype.card ι := by
  have hv : (∑ i, V i) ≤ (2 * W) * Fintype.card ι := by
    calc
      _ ≤ ∑ _i : ι, 2 * W := sum_le_sum (fun i _ => hV i)
      _ = _ := by simp; ring
  rw [sum_add_distrib]
  exact (add_le_add hdegree hv).trans_eq (by ring)

/-- The sitewise estimate `sum_d a_d(n)^2 ≤ (8W)^J`, with actual
one-prime-per-family products and a total lit-prime degree at most `6WJ`. -/
theorem squared_center_products_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → Type*} [∀ i, Fintype (P i)]
    (θ : (i : ι) → P i → ℝ) (lit : (i : ι) → P i → Bool)
    (W : ℝ)
    (hθ : ∀ i p, 0 ≤ θ i p) (hθ1 : ∀ i p, θ i p ≤ 1)
    (hV : ∀ i, ∑ p, θ i p ≤ 2 * W)
    (hdegree : (∑ i, ∑ p : P i, if lit i p then (1 : ℝ) else 0) ≤
      6 * W * Fintype.card ι) :
    (∑ x : (i : ι) → P i, (∏ i, centerMagnitude (θ i (x i)) (lit i (x i))) ^ 2) ≤
      (8 * W) ^ Fintype.card ι := by
  classical
  apply (squared_center_products_le_product θ lit hθ hθ1).trans
  apply nonneg_product_le_power_card
  · intro i
    exact add_nonneg (sum_nonneg (fun p _ => by split_ifs <;> norm_num))
      (sum_nonneg (fun p _ => hθ i p))
  · exact sum_degree_budget (fun i => ∑ p : P i, if lit i p then (1 : ℝ) else 0)
      (fun i => ∑ p, θ i p) W hV hdegree

end TwoPointCorrelations

end OAI
