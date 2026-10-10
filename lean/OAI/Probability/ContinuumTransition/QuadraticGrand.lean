import OAI.Probability.ContinuumTransition.LaplaceEventual

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable def quadraticGrandTerm (φ : ℝ → ℝ) (β μ a L : ℝ) (n : ℕ) : ℝ :=
  Real.exp (μ*n+a*(n : ℝ)^2/L^3)*partition φ β L n

theorem quadraticGrandTerm_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (μ a : ℝ) (n : ℕ) : 0 < quadraticGrandTerm φ β μ a L n :=
  mul_pos (Real.exp_pos _) (partition_pos hφ hβ hL hst n)

theorem log_quadraticGrandTerm {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hst : ∀ (n : ℕ) (x : Fin n → Space), ((-B*n : ℝ) : EReal) ≤ energy φ x)
    (μ a : ℝ) (n : ℕ) :
    Real.log (quadraticGrandTerm φ β μ a L n)/L^3 =
      μ*((n : ℝ)/L^3)+a*((n : ℝ)/L^3)^2-finiteCanonical φ β L n := by
  rw [quadraticGrandTerm, Real.log_mul (Real.exp_pos _).ne' (partition_pos hφ hβ hL hst n).ne',
    Real.log_exp]
  unfold finiteCanonical
  ring

theorem quadraticGrandTerm_high_density {t β L μ a : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3) {n : ℕ}
    (hn : Real.exp (μ+β*t^2/2+2) ≤ (n : ℝ)/L^3) :
    quadraticGrandTerm (physicalProfile t σ R) β μ a L n ≤ (Real.exp (-1))^n := by
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  have he := finiteCanonical_lower_coercive ht hβ hL hσ hR hs hsmall n
  have hd : 0 ≤ (n : ℝ)/L^3 := div_nonneg (Nat.cast_nonneg _) (pow_pos hL 3).le
  have hl := Real.log_le_log (Real.exp_pos (μ+β*t^2/2+2)) hn
  rw [Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_right hl hd
  have hq := mul_le_mul_of_nonneg_right ha (sq_nonneg ((n : ℝ)/L^3))
  have hb : μ*((n : ℝ)/L^3)+a*((n : ℝ)/L^3)^2-
      finiteCanonical (physicalProfile t σ R) β L n ≤ -((n : ℝ)/L^3) := by
    rw [mul_div_assoc] at hq
    nlinarith only [he, hm, hq]
  rw [← log_quadraticGrandTerm hφ hβ hL hst μ a n, ← neg_div] at hb
  have hh := (div_le_div_iff_of_pos_right (pow_pos hL 3)).1 hb
  rw [← Real.exp_nat_mul]
  apply (Real.log_le_iff_le_exp (quadraticGrandTerm_pos hφ hβ hL hst μ a n)).1
  simpa using hh

theorem summable_quadraticGrandTerm {t β L μ a : ℝ} (ht : 0 ≤ t) (hβ : 0 ≤ β) (hL : 0 < L)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8)
    (ha : a ≤ β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/L)^3) :
    Summable (quadraticGrandTerm (physicalProfile t σ R) β μ a L) := by
  have hb : Summable (fun n : ℕ => (Real.exp (-1))^n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simp)
  apply hb.of_norm_bounded_eventually_nat
  have hn := ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_div_const
    (pow_pos hL 3)).eventually (eventually_ge_atTop (Real.exp (μ+β*t^2/2+2)))
  filter_upwards [hn] with n hn
  have hφ := measurable_radialPotential (measurable_physicalProfile t hσ hR hs)
  have hst := physicalProfile_stable ht hσ hR hs hsmall
  rw [Real.norm_eq_abs, abs_of_pos (quadraticGrandTerm_pos hφ hβ hL hst μ a n)]
  exact quadraticGrandTerm_high_density ht hβ hL hσ hR hs hsmall ha hn

end ContinuumTemperature
end

end OAI
