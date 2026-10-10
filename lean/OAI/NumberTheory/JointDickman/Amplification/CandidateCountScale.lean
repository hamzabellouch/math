import OAI.NumberTheory.JointDickman.Amplification.RegularWeightCap

namespace OAI

/-! # A regular endpoint admits only polynomially many subset choices -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem RegularPrimeSet.total_upper {B L : ℕ} {τ C : ℝ} {S : Finset ℕ}
    (h : RegularPrimeSet B L τ C S) (hL : 1 ≤ L) :
    (S.card : ℝ) ≤ (1/2+τ)*auxiliaryLogLength B := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  simpa only [div_self hL0,primePrefix,lt_self_iff_false,ite_false] using
    (h.1 L (mem_Icc.mpr ⟨hL,le_rfl⟩)).2

theorem regular_union_count {B L : ℕ} {τ C : ℝ} {S R : Finset ℕ}
    (hS : RegularPrimeSet B L τ C S) (hR : RegularPrimeSet B L τ C R) (hL : 1 ≤ L) :
    ((S ∪ R).card : ℝ) ≤ (1+2*τ)*auxiliaryLogLength B := by
  have hcard : ((S ∪ R).card : ℝ) ≤ (S.card : ℝ)+(R.card : ℝ) := by
    exact_mod_cast card_union_le S R
  have hs := hS.total_upper hL
  have hr := hR.total_upper hL
  nlinarith only [hcard,hs,hr]

theorem regular_endpoint_subset_count {L : ℕ} (hL : 1 ≤ L) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∀ᶠ B : ℕ in atTop, ∀ C : ℝ, ∀ S R : Finset ℕ,
      RegularPrimeSet B L τ C S → RegularPrimeSet B L τ C R →
        2^(S ∪ R).card ≤ B := by
  have hlog2 := Real.log_two_lt_d9
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc0 : 0 ≤ (1+2*τ)*Real.log 2 := mul_nonneg (by linarith) hlog20
  have hc1 : (1+2*τ)*Real.log 2 ≤ 1 := by
    have ht : τ ≤ 1/1000 := hτsmall
    have hm := mul_le_mul_of_nonneg_right ht hlog20
    nlinarith
  filter_upwards [auxiliaryRatio_tendsto.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_gt_atTop 1] with B hR hlog hB
  intro C S R hS hSR
  change 1 ≤ Real.log (B : ℝ) at hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (lt_trans Nat.zero_lt_one hB)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB.le
  have hRB : auxiliaryRatio B ≤ (B : ℝ) := by
    unfold auxiliaryRatio
    apply div_le_self hB0.le
    linarith only [hlog]
  have hcount := regular_union_count hS hSR hL
  have hp : (2 : ℝ)^(S ∪ R).card ≤ (B : ℝ) := by
    calc
      _ = Real.exp (Real.log 2*((S ∪ R).card : ℝ)) := by
        rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num)]
      _ ≤ Real.exp (Real.log 2*((1+2*τ)*auxiliaryLogLength B)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcount hlog20)
      _ = (auxiliaryRatio B)^((1+2*τ)*Real.log 2) := by
        rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hR)]
        unfold auxiliaryLogLength
        congr 1
        ring
      _ ≤ (B : ℝ)^((1+2*τ)*Real.log 2) :=
        Real.rpow_le_rpow (by linarith only [hR]) hRB hc0
      _ ≤ (B : ℝ)^((1 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hB1 hc1
      _ = _ := Real.rpow_one _
  exact_mod_cast hp

end JointDickman

end OAI
