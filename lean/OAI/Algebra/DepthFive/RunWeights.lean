import Mathlib

namespace OAI

/-! Analytic weight estimates for the D-runs in the path-type sum. -/

open scoped BigOperators
noncomputable section
namespace Problem335
namespace RunWeights

/-- The interval discrepancy estimate converts directly into a bound on its weight. -/
lemma interval_weight_le {α β ρ ε N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hβ : 0 ≤ β) (hβupper : β ≤ α ^ ρ * Real.exp ε)
    (hscale : α ^ (-(1 + ρ)) ≤ N) (v u : ℕ)
    (hdiscrepancy : (v : ℝ) - ρ * u ≤ 1 + ρ) :
    α ^ (-(v : ℝ)) * β ^ u ≤ N * Real.exp (ε * u) := by
  have hp : β ^ u ≤ (α ^ ρ * Real.exp ε) ^ u := by gcongr
  calc
    α ^ (-(v : ℝ)) * β ^ u ≤
        α ^ (-(v : ℝ)) * (α ^ ρ * Real.exp ε) ^ u := by
      exact mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hα.le _)
    _ = α ^ (-(v : ℝ) + ρ * u) * Real.exp (ε * u) := by
      rw [mul_pow, ← Real.rpow_natCast (α ^ ρ) u,
        ← Real.rpow_mul hα.le, ← Real.exp_nat_mul]
      rw [mul_comm (u : ℝ) ε, ← mul_assoc, ← Real.rpow_add hα]
    _ ≤ α ^ (-(1 + ρ)) * Real.exp (ε * u) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
    _ ≤ N * Real.exp (ε * u) := by
      exact mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le

/-- The parameter bound on alpha controls the common cost of every run. -/
lemma scale_le_of_inv_le_sqrt {α ρ N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hρ : ρ ≤ 1) (hN : 0 ≤ N) (hinv : α⁻¹ ≤ Real.sqrt N) :
    α ^ (-(1 + ρ)) ≤ N := by
  calc
    α ^ (-(1 + ρ)) ≤ α ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hα hα1 (by linarith)
    _ = (α⁻¹) ^ 2 := by
      rw [show (-2 : ℝ) = (-1) * 2 by norm_num, Real.rpow_mul hα.le,
        Real.rpow_two, Real.rpow_neg_one]
    _ ≤ (Real.sqrt N) ^ 2 := by gcongr
    _ = N := Real.sq_sqrt hN

lemma interval_weight_le_of_inv_le_sqrt {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hρ : ρ ≤ 1)
    (hN : 0 ≤ N) (hinv : α⁻¹ ≤ Real.sqrt N) (v u : ℕ)
    (hdiscrepancy : (v : ℝ) - ρ * u ≤ 1 + ρ) :
    α ^ (-(v : ℝ)) * β ^ u ≤ N * Real.exp (ε * u) :=
  interval_weight_le hα hα1 hβ hβupper
    (scale_le_of_inv_le_sqrt hα hα1 hρ hN hinv) v u hdiscrepancy

/-- Multiplying the run estimates accumulates only their total number of U layers. -/
lemma prod_interval_weight_le {ι : Type*} (S : Finset ι) {α β ρ ε N : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β)
    (hβupper : β ≤ α ^ ρ * Real.exp ε) (hscale : α ^ (-(1 + ρ)) ≤ N)
    (v u : ι → ℕ) (hdiscrepancy : ∀ i ∈ S, (v i : ℝ) - ρ * u i ≤ 1 + ρ) :
    (∏ i ∈ S, α ^ (-(v i : ℝ)) * β ^ u i) ≤
      N ^ S.card * Real.exp (ε * ∑ i ∈ S, (u i : ℝ)) := by
  calc
    (∏ i ∈ S, α ^ (-(v i : ℝ)) * β ^ u i) ≤
        ∏ i ∈ S, N * Real.exp (ε * u i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        exact interval_weight_le hα hα1 hβ hβupper hscale (v i) (u i)
          (hdiscrepancy i hi)
    _ = N ^ S.card * Real.exp (ε * ∑ i ∈ S, (u i : ℝ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.mul_sum]

lemma one_add_pow_le_exp (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (1 + x) ^ k ≤ Real.exp ((k : ℝ) * x) := by
  rw [Real.exp_nat_mul]
  gcongr
  linarith [Real.add_one_le_exp x]

/-- The isolated-position correction prefactor costs at most exp(3 sqrt N). -/
lemma correction_prefactor_le_exp {N a : ℝ} (hN : 1 ≤ N)
    (ha : 0 ≤ a) (haN : a ≤ Real.sqrt N) (k : ℕ) (hk : 2 * (k : ℝ) ≤ N) :
    (1 + 2 / N ^ 2) ^ k * (1 + a) * (1 + a / N) ^ k ≤
      Real.exp (3 * Real.sqrt N) := by
  have hNpos : 0 < N := by linarith
  have hsqrt : 1 ≤ Real.sqrt N := by
    simpa using Real.sqrt_le_sqrt hN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkN : (k : ℝ) ≤ N := by linarith
  have hfirst : (k : ℝ) * (2 / N ^ 2) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos hNpos)).2
    nlinarith
  have hthird : (k : ℝ) * (a / N) ≤ a := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hNpos).2
    nlinarith
  calc
    (1 + 2 / N ^ 2) ^ k * (1 + a) * (1 + a / N) ^ k ≤
        Real.exp ((k : ℝ) * (2 / N ^ 2)) * Real.exp a *
          Real.exp ((k : ℝ) * (a / N)) := by
      gcongr
      · exact one_add_pow_le_exp _ (by positivity) k
      · linarith [Real.add_one_le_exp a]
      · exact one_add_pow_le_exp _ (by positivity) k
    _ = Real.exp ((k : ℝ) * (2 / N ^ 2) + a + (k : ℝ) * (a / N)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (3 * Real.sqrt N) := Real.exp_le_exp.mpr (by linarith)

/-- Pointwise U-layer corrections cost at most exp(2 sqrt N). -/
lemma u_correction_le_exp {N β : ℝ} (hN : 0 < N) (hβ : 0 ≤ β)
    (hβN : β ≤ 2 / Real.sqrt N) (m : ℕ) (hm : (m : ℝ) ≤ N) :
    (1 + β) ^ m ≤ Real.exp (2 * Real.sqrt N) := by
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hsquare := Real.sq_sqrt hN.le
  have hmul : (m : ℝ) * β ≤ N * (2 / Real.sqrt N) := by gcongr
  have heq : N * (2 / Real.sqrt N) = 2 * Real.sqrt N := by
    rw [← mul_div_assoc]
    apply (div_eq_iff hsqrt.ne').2
    nlinarith
  exact (one_add_pow_le_exp β hβ m).trans
    (Real.exp_le_exp.mpr (heq ▸ hmul))

/-- Surviving N-layers have a small correction, except possibly at one endpoint. -/
lemma correction_product_le {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (e : ι) (h : ι → ℕ) {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (k : ℕ) (hcard : T.card ≤ k)
    (hinterior : ∀ i ∈ T, i ≠ e → 1 ≤ h i) :
    (∏ i ∈ T, (1 + a * (N⁻¹) ^ h i)) ≤ (1 + a) * (1 + a / N) ^ k := by
  have hNpos : 0 < N := by linarith
  have hinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hinv1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
  have hbase : 1 ≤ 1 + a / N := le_add_of_nonneg_right (by positivity)
  have hall (i : ι) : 1 + a * N⁻¹ ^ h i ≤ 1 + a := by
    have hp : N⁻¹ ^ h i ≤ 1 := pow_le_one₀ hinv0 hinv1
    nlinarith
  have hsmall (i : ι) (hi : i ∈ T) (hie : i ≠ e) :
      1 + a * N⁻¹ ^ h i ≤ 1 + a / N := by
    have hp := pow_le_pow_of_le_one hinv0 hinv1 (hinterior i hi hie)
    simp only [pow_one] at hp
    rw [div_eq_mul_inv]
    nlinarith
  by_cases he : e ∈ T
  · rw [← Finset.mul_prod_erase T (fun i => 1 + a * N⁻¹ ^ h i) he]
    have hp : (∏ i ∈ T.erase e, (1 + a * N⁻¹ ^ h i)) ≤ (1 + a / N) ^ k := by
      calc
        (∏ i ∈ T.erase e, (1 + a * N⁻¹ ^ h i)) ≤ ∏ _i ∈ T.erase e, (1 + a / N) := by
          apply Finset.prod_le_prod₀
          · intro i hi; positivity
          · intro i hi
            exact hsmall i (Finset.mem_erase.mp hi).2 (Finset.mem_erase.mp hi).1
        _ = (1 + a / N) ^ (T.erase e).card := by rw [Finset.prod_const]
        _ ≤ (1 + a / N) ^ k :=
          pow_le_pow_right₀ hbase (Finset.card_erase_le.trans hcard)
    exact mul_le_mul (hall e) hp (by positivity) (by positivity)
  · have hp : (∏ i ∈ T, (1 + a * N⁻¹ ^ h i)) ≤ (1 + a / N) ^ k := by
      calc
        (∏ i ∈ T, (1 + a * N⁻¹ ^ h i)) ≤ ∏ _i ∈ T, (1 + a / N) := by
          apply Finset.prod_le_prod₀
          · intro i hi; positivity
          · intro i hi
            apply hsmall i hi
            intro hie
            exact he (hie ▸ hi)
        _ = (1 + a / N) ^ T.card := by rw [Finset.prod_const]
        _ ≤ (1 + a / N) ^ k := pow_le_pow_right₀ hbase hcard
    exact hp.trans (by nlinarith [show (0 : ℝ) ≤ (1 + a / N) ^ k by positivity])

end RunWeights
end Problem335

end

end OAI
