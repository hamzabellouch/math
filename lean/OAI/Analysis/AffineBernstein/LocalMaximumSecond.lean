import Mathlib

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology

/-- The second-order necessary condition, proved from the local Taylor
remainder. No elliptic estimate is hidden in the maximum principle step. -/
lemma localMax_second_deriv_nonpos {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 2 f 0) (hm : IsLocalMax f 0) : deriv (deriv f) 0 ≤ 0 := by
  obtain ⟨U,hU,hc⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  let I : Set ℝ := Ioo (-r) r
  have h0 : (0:ℝ) ∈ I := ⟨by linarith,hr⟩
  have hIU : I ⊆ U := by
    intro t ht
    apply hrU
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt] using (show -r < t ∧ t < r from ht)
  have hI : IsOpen I := isOpen_Ioo
  have hcI : ContDiffOn ℝ 2 f I := hc.mono hIU
  have hid (k : ℕ) (hk : k ≤ 2) : iteratedDerivWithin k f I 0 = iteratedDeriv k f 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hI.uniqueDiffOn (hf.of_le (by exact_mod_cast hk)) h0
  have hz := hm.deriv_eq_zero
  have hpoly (t : ℝ) : taylorWithinEval f 2 I 0 t =
      f 0 + (deriv (deriv f) 0 / 2) * t^2 := by
    simp only [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hid 0 (by omega),hid 1 (by omega),hid 2 (by omega)]
    simp only [iteratedDeriv_zero, iteratedDeriv_succ, hz,
      Nat.factorial_zero, Nat.factorial_succ, Nat.cast_one,
      Nat.cast_mul, sub_zero, pow_zero, pow_one, smul_eq_mul]
    ring
  have ht := Real.taylor_tendsto (show Convex ℝ I from convex_Ioo _ _) h0 hcI
  rw [nhdsWithin_eq_nhds.mpr (hI.mem_nhds h0)] at ht
  simp only [hpoly,sub_zero] at ht
  have ht' := ht.mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ) from nhdsWithin_le_nhds)
  have hle : (0:ℝ) ≤ -(deriv (deriv f) 0 / 2) := by
    apply le_of_tendsto ht'
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hne
    have htne : t ≠ 0 := hne
    apply (div_le_iff₀ (sq_pos_of_ne_zero htne)).mpr
    nlinarith
  linarith

end AffineBernstein

end

end OAI
