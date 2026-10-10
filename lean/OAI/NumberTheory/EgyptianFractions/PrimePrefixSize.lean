import Mathlib

namespace OAI
noncomputable section
open Filter Topology

namespace Problem337.PrimePrefixSize

/-- Crossing the square-root cutoff forces a large prefix if the next prime is small. -/
lemma log_prefix_lower {d p Y v : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hY : 0 < Y)
    (hYlog : v / 2 ≤ Real.log Y)
    (hcross : Real.sqrt Y < d * p)
    (hplog : Real.log p < v ^ (15 / 16 : ℝ))
    (hsmall : v ^ (15 / 16 : ℝ) ≤ v / 20) :
    v / 5 < Real.log d := by
  have hc := Real.log_lt_log (Real.sqrt_pos.2 hY) hcross
  rw [Real.log_sqrt hY.le, Real.log_mul hd.ne' hp.ne'] at hc
  linarith

lemma exp_prefix_lower {d p Y v : ℝ}
    (hd : 0 < d) (hp : 0 < p) (hY : 0 < Y)
    (hYlog : v / 2 ≤ Real.log Y)
    (hcross : Real.sqrt Y < d * p)
    (hplog : Real.log p < v ^ (15 / 16 : ℝ))
    (hsmall : v ^ (15 / 16 : ℝ) ≤ v / 20) :
    Real.exp (v / 5) < d := by
  calc
    Real.exp (v / 5) < Real.exp (Real.log d) := Real.exp_lt_exp.mpr
      (log_prefix_lower hd hp hY hYlog hcross hplog hsmall)
    _ = d := Real.exp_log hd

lemma eventually_fifteen_sixteenths_small :
    ∀ᶠ v : ℝ in atTop, v ^ (15 / 16 : ℝ) ≤ v / 20 := by
  have hlim := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)
  have he := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20))
  filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with v hv hvpos
  calc
    v ^ (15 / 16 : ℝ) = v ^ (1 : ℝ) * v ^ (-(1 / 16 : ℝ)) := by
      rw [← Real.rpow_add hvpos]
      norm_num
    _ = v * v ^ (-(1 / 16 : ℝ)) := by rw [Real.rpow_one]
    _ ≤ v * (1 / 20) := mul_le_mul_of_nonneg_left hv.le hvpos.le
    _ = v / 20 := by ring

/-- The manuscript's lower scale tends uniformly beyond every fixed threshold. -/
lemma eventually_uniform_lower_scale (V : ℝ) :
    ∀ᶠ S : ℝ in atTop, ∀ v : ℝ, S / (2 * Real.log S) ≤ v → V ≤ v := by
  let W := max V 1
  have hW : 0 < W := by dsimp [W]; positivity
  have he := Real.isLittleO_log_id_atTop.bound (by positivity : 0 < 1 / (2 * W))
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with S hS hS2
  have hSpos : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  simp only [Real.norm_eq_abs, abs_of_pos hlog, id_eq, abs_of_pos hSpos] at hS
  have hmul : (2 * W) * Real.log S ≤ S := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * W)).1
      (show Real.log S ≤ S / (2 * W) by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hS)
    nlinarith
  intro v hv
  have hWv : W ≤ S / (2 * Real.log S) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log S)).2
    nlinarith
  exact (le_max_left _ _).trans (hWv.trans hv)

/-- Uniform prefix-size conclusion over all admissible divisor-moment scales. -/
theorem eventually_uniform_prefix_large :
    ∀ᶠ S : ℝ in atTop, ∀ v d p Y : ℝ,
      S / (2 * Real.log S) ≤ v →
      0 < d → 0 < p → 0 < Y → v / 2 ≤ Real.log Y →
      Real.sqrt Y < d * p → Real.log p < v ^ (15 / 16 : ℝ) →
      Real.exp (v / 5) < d := by
  obtain ⟨V, hV⟩ := eventually_atTop.mp eventually_fifteen_sixteenths_small
  filter_upwards [eventually_uniform_lower_scale V] with S hS
  intro v d p Y hv hd hp hY hYlog hcross hplog
  exact exp_prefix_lower hd hp hY hYlog hcross hplog (hV v (hS v hv))

end Problem337.PrimePrefixSize

end

end OAI
