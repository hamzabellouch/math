import OAI.MeasureTheory.Falconer.Geometry.ScalarNetIteration

namespace OAI

/-! A power-scale interval net becomes a full-scale net after a number
of scalar ring operations depending only on the power. -/
namespace Falconer

 theorem scalar_power_net_amplification {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ∀ δ η : ℝ, 0 < δ → δ ≤ 1 → 0 < η → η ≤ 1/8 →
      5*η ≤ δ^c → ∀ S : Finset ℝ, 0 ∈ S →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ a ∈ S, |x-a| ≤ η) →
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
        ∃ a ∈ scalarCoefficientClosure S k, |x-a| ≤ δ := by
  have hevent := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually
    (Filter.eventually_gt_atTop (1/c))
  obtain ⟨n,hn⟩ := hevent.exists
  have hexp : 1 ≤ c*((2:ℝ)^n) := by
    have hh := mul_lt_mul_of_pos_left hn hc
    have he : c*(1/c) = 1 := by field_simp
    rw [he] at hh
    exact hh.le
  refine ⟨2*n,?_⟩
  intro δ η hδ hδ1 hη hη1 hηc S hzero hnet x hx0 hx1
  obtain ⟨a,ha,hea⟩ := scalar_interval_net_iterate hη hη1 S hzero hnet n x hx0 hx1
  refine ⟨a,ha,hea.trans ?_⟩
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 5*η) hηc (2^n)
  have he : (δ^c)^(2^n) = δ^(c*((2:ℝ)^n)) := by
    rw [← Real.rpow_natCast (δ^c) (2^n),← Real.rpow_mul hδ.le,Nat.cast_pow,Nat.cast_ofNat]
  rw [he] at hp
  have hs : δ^(c*((2:ℝ)^n)) ≤ δ := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hexp
  rw [scalarNetError_formula]
  exact (div_le_div_of_nonneg_right (hp.trans hs) (by norm_num : (0 : ℝ) ≤ 5)).trans (by linarith)

end Falconer

end OAI
