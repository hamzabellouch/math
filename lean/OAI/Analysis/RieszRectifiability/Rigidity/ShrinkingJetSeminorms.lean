import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.VanishingJetGrowth
import OAI.Analysis.RieszRectifiability.Limits.SchwartzCutoffConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open SchwartzMap Metric Set Filter Topology
open scoped ContDiff

def jetCutoffCoefficient (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * C i * 2 ^ (i + 1)

theorem jetCutoffCoefficient_nonneg (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (n : ℕ) :
    0 ≤ jetCutoffCoefficient C n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hC i)) (by positivity)

theorem inverse_scale_cancel (r : ℝ) (hr : 0 < r) (i : ℕ) :
    (r⁻¹) ^ i * (2 * r) ^ (i + 1) = 2 ^ (i + 1) * r := by
  rw [mul_pow, pow_succ r]
  calc
    _ = 2 ^ (i + 1) * ((r⁻¹) ^ i * r ^ i) * r := by ring
    _ = _ := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow, mul_one]

theorem zero_jet_localized_derivative_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0)
    (q : Ambient d → ℝ) (hq : ContDiff ℝ ∞ q)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (r : ℝ) (hr : 0 < r)
    (hb : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i * (r⁻¹) ^ i)
    (x : Ambient d) (hx : ‖x‖ ≤ 2 * r) :
    ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖ ≤
      SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r := by
  let M := SchwartzMap.seminorm ℝ 0 (n + 1) g
  have hM : 0 ≤ M := apply_nonneg _ _
  have hd := norm_iteratedFDeriv_smul_le hq (g.smooth ⊤) x (n := n) (mod_cast le_top)
  apply hd.trans
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), M * ((n.choose i : ℝ) * C i * 2 ^ (i + 1)) * r := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using! hi
      have hg : ‖iteratedFDeriv ℝ (n - i) g x‖ ≤ M * (2 * r) ^ (i + 1) := by
        have ht := schwartz_zero_jet_derivative_bound g n (n - i) (by omega) hz x
        rw [show n + 1 - (n - i) = i + 1 by omega] at ht
        exact ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx _) hM)
      calc
        _ ≤ (n.choose i : ℝ) * (C i * (r⁻¹) ^ i) * (M * (2 * r) ^ (i + 1)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hb i x) (by positivity)) hg
            (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (hC i) (by positivity)))
        _ = M * ((n.choose i : ℝ) * C i) * ((r⁻¹) ^ i * (2 * r) ^ (i + 1)) := by ring
        _ = _ := by rw [inverse_scale_cancel r hr i]; ring
    _ = _ := by
      unfold jetCutoffCoefficient
      rw [Finset.mul_sum, Finset.sum_mul]

theorem zero_jet_localized_seminorm_bound {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : 𝓢(Ambient d, F)) (k n : ℕ)
    (hz : ∀ i, i ≤ n → iteratedFDeriv ℝ i g 0 = 0)
    (q : Ambient d → ℝ) (hq : q.HasTemperateGrowth)
    (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) (r : ℝ) (hr : 0 < r) (hrsmall : 2 * r ≤ 1)
    (hb : ∀ i x, ‖iteratedFDeriv ℝ i q x‖ ≤ C i * (r⁻¹) ^ i)
    (hs : tsupport q ⊆ closedBall (0 : Ambient d) (2 * r)) :
    SchwartzMap.seminorm ℝ k n (smulLeftCLM F q g) ≤
      SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r := by
  have hnonneg : 0 ≤ SchwartzMap.seminorm ℝ 0 (n + 1) g * jetCutoffCoefficient C n * r :=
    mul_nonneg (mul_nonneg (apply_nonneg _ _) (jetCutoffCoefficient_nonneg C hC n)) hr.le
  apply seminorm_le_bound ℝ k n _ hnonneg
  intro x
  rw [smulLeftCLM_apply hq]
  by_cases hx : x ∈ closedBall (0 : Ambient d) (2 * r)
  · have hxr : ‖x‖ ≤ 2 * r := by simpa only [mem_closedBall, dist_zero_right] using! hx
    calc
      _ ≤ 1 * ‖iteratedFDeriv ℝ n (fun y => q y • g y) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) (hxr.trans hrsmall)) (norm_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact zero_jet_localized_derivative_bound g n hz q hq.1 C hC r hr hb x hxr
  · have hnot : x ∉ tsupport q := fun h => hx (hs h)
    have heq : (fun y => q y • g y) =ᶠ[𝓝 x] (fun _ => (0 : F)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ n).eq_of_nhds
    rw [hd]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using! hnonneg

end

end RieszRectifiability

end OAI
