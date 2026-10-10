import OAI.Analysis.IrrationalRotation.Rotation.CircleParameterBlocks
import OAI.Analysis.IrrationalRotation.Sampling.MixedRadixCircle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

noncomputable section
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coupling_K_ge (j : ℕ) (hj : 1 ≤ j) : 100 ≤ p.K j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => simpa using hp.initial_K.ge
  | succ n ih =>
    have h := hp.K_double (1 + n) (by omega)
    have he : 1 + (n + 1) = 1 + n + 1 := by omega
    rw [he]
    omega

omit hp in
lemma coupling_kappa_bounds (j : ℕ) (hj : 1 ≤ j) :
    0 ≤ kappa j ∧ kappa j ≤ 1 / 100 := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  unfold kappa
  constructor
  · positivity
  · apply one_div_le_one_div_of_le (by norm_num)
    nlinarith

lemma coupling_a_bounds (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.m j : ℝ) ≤ p.a j ∧ p.a j ≤ 1 / 4 := by
  have hm : (0 : ℝ) < p.m j := by exact_mod_cast hp.m_pos j hj
  have hG : (1 : ℝ) ≤ p.G j := by exact_mod_cast hp.G_pos j hj
  have hGm : 4 * (p.G j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_G j hj
  unfold a
  exact ⟨div_le_div_of_nonneg_right hG hm.le, (div_le_iff₀ hm).mpr (by linarith)⟩

lemma coupling_b_bounds (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.m j : ℝ) ≤ p.b j ∧ p.b j ≤ 1 / 4 := by
  have hm : (200 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_200 j hj
  have hm1 : (1 : ℝ) ≤ p.m j := by linarith
  have hm0 : (0 : ℝ) < p.m j := by linarith
  constructor
  · simpa only [b, one_div, Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le hm1 (show (-1 : ℝ) ≤ -(19 / 20 : ℝ) by norm_num))
  · have hs : (4 : ℝ) ≤ Real.sqrt (p.m j) := by
      apply (Real.le_sqrt (by norm_num) hm0.le).mpr
      nlinarith
    have hpw : (4 : ℝ) ≤ (p.m j : ℝ) ^ (19 / 20 : ℝ) := by
      calc
        _ ≤ Real.sqrt (p.m j) := hs
        _ = (p.m j : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
    rw [b, Real.rpow_neg hm0.le, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) hpw

lemma coupling_radix_ge_N {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    p.N s ≤ (MixedRadix.radices p.q i : ℝ) := by
  simpa only [MixedRadix.radices, Nat.cast_div (hp.frequency_divisible i)
    (by exact_mod_cast (Nat.ne_of_gt (hp.q_pos i)) : (p.q i : ℝ) ≠ 0)] using hp.frequency_ratios s hs i hi

lemma coupling_bin_small {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s)
    {w : ℝ} (hw : 1 / (p.m s : ℝ) ≤ w) :
    1 / (MixedRadix.radices p.q i : ℝ) < w / 2 := by
  have hm : (0 : ℝ) < p.m s := by exact_mod_cast hp.m_pos s hs
  have hk : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
  have hN : (0 : ℝ) < p.N s := by unfold N; positivity
  have hmN : 2 * (p.m s : ℝ) < p.N s := by unfold N; nlinarith
  calc
    _ ≤ 1 / p.N s := one_div_le_one_div_of_le hN (hp.coupling_radix_ge_N hs hi)
    _ < (1 / (p.m s : ℝ)) / 2 := by
      rw [div_div]
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    _ ≤ _ := div_le_div_of_nonneg_right hw (by norm_num)

end Invariant233.CircleParameterLaws

end

end OAI
