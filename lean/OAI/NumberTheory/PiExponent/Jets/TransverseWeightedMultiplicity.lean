import OAI.NumberTheory.PiExponent.Approximation.RectangularVolume
import OAI.NumberTheory.PiExponent.Approximation.WeightSeparationConstant
import OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity

namespace OAI

noncomputable section
namespace PiExponent.TransverseWeightedMultiplicity

open scoped BigOperators

theorem eventually_uniform_rectangularCutoff_two_le (m : ℕ)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℝ in Filter.atTop, ∀ k : ℕ, 0 < k → k ≤ m →
      ∀ B : Fin k → Fin (m + 1), ∀ i,
        2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i := by
  have ht : Filter.Tendsto (fun N : ℝ => epsilon * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℝ in Filter.atTop, ∀ j : Fin (m + 1),
      (m : ℝ) * cost j < epsilon * N :=
    Filter.eventually_all.mpr (fun j =>
      ht.eventually (Filter.eventually_gt_atTop ((m : ℝ) * cost j)))
  filter_upwards [hb] with N hN
  intro k hk hkm B i
  have hdim : (k : ℝ) ≤ m := by exact_mod_cast hkm
  apply two_le_rectangularCutoff hk (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right hdim (hcost _).le).trans_lt (hN (B i))

theorem rectangularCutoff_budget {k : ℕ} (hk : 0 < k)
    (kappa : Fin k → ℝ) (hkappa : ∀ i, 0 < kappa i)
    (T : ℝ) (hT : 0 < T) :
    ∑ i, ((rectangularCutoff kappa T i - 1 : ℕ) : ℝ) * kappa i ≤ T := by
  have hpos := rectangularCutoff_pos hk kappa hkappa hT
  have hlt : ∀ i, rectangularCutoff kappa T i - 1 < rectangularCutoff kappa T i := by
    intro i
    exact Nat.sub_lt (hpos i) (by norm_num)
  have h := rectangularCutoff_weight_lt hk kappa hkappa
    (fun i => rectangularCutoff kappa T i - 1) hlt
  simpa only [mul_comm] using h.le

theorem rectangular_weight_product_comparison {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N L : ℝ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (epsilon * N) ^ k / ((k : ℝ) ^ k * ∏ i, kappa i) ≤ L)
    (hupper : L ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  have hA : 0 < ∏ i, rho i := Finset.prod_pos (fun i _ => hrho i)
  have hB : 0 < (k : ℝ) ^ k * ∏ i, kappa i :=
    mul_pos (pow_pos (by exact_mod_cast hk) _) (Finset.prod_pos (fun i _ => hkappa i))
  have h := (div_le_div_iff₀ hB hA).mp (hlower.trans hupper)
  rw [mul_pow] at h
  apply (le_div_iff₀ (pow_pos hepsilon k)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hN k)).mp
  calc
    N ^ k * ((∏ i, rho i) * epsilon ^ k) =
        epsilon ^ k * N ^ k * ∏ i, rho i := by ring
    _ ≤ N ^ k * ((k : ℝ) ^ k * ∏ i, kappa i) := h

theorem weight_comparison_of_rectangular_count {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N : ℝ) (L : ℕ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (∏ i, rectangularCutoff kappa (epsilon * N) i : ℕ) ≤ L)
    (hupper : (L : ℝ) ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  apply rectangular_weight_product_comparison hk rho kappa epsilon N L
    hrho hkappa hepsilon hN _ hupper
  have hv := rectangularCutoff_product_lower hk kappa hkappa (mul_pos hepsilon hN)
  apply hv.trans
  exact_mod_cast hlower

theorem rectangular_comparison_le_separation_constant {m k : ℕ}
    (hkm : k ≤ m) (kappa : Fin k → ℝ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkappa : ∀ i, 0 ≤ kappa i) :
    (k : ℝ) ^ k * (∏ i, kappa i) / (sigma / ((m : ℝ) + 2)) ^ k ≤
      (2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)) * ∏ i, kappa i := by
  have h := PiExponentApprox.rectangular_multiplicity_constant_le_enlarged
    m k sigma hsigma hkm
  have hp : 0 ≤ ∏ i, kappa i := Finset.prod_nonneg (fun i _ => hkappa i)
  have hh := mul_le_mul_of_nonneg_right h hp
  convert hh using 1
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ring

end PiExponent.TransverseWeightedMultiplicity
end

end OAI
