import OAI.Analysis.StrictMeans.CircleBounds

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower

end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma dyadic_norm_power_bound {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ‖dyadicOperator^n‖ ≤ C * (dyadicHeight n)^(-b) := by
  have hb0 : 0 < b := lt_of_le_of_lt dyadicExponent_nonneg hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : dyadicLogGrowth < b*Real.log 2 := (div_lt_iff₀ hl2).mp hb
  obtain ⟨N,hN⟩ := eventually_atTop.mp (normPower_eventually_le_exp
    dyadicOperator dyadicOperator_pow_norm_ge_one he)
  let C : ℝ := 1 + ∑ i ∈ Finset.range N, ‖dyadicOperator^i‖
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg (dyadicOperator^i)))
  refine ⟨C,lt_of_lt_of_le zero_lt_one hC,?_⟩
  intro n
  have hexp : Real.exp ((b*Real.log 2)*n) = (dyadicHeight n)^(-b) := by
    rw [Real.rpow_def_of_pos (dyadicHeight_pos n)]
    unfold dyadicHeight
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    congr 1
    ring
  have hpos : 1 ≤ Real.exp ((b*Real.log 2)*n) :=
    Real.one_le_exp (by positivity)
  rw [← hexp]
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hle : ‖dyadicOperator^n‖ ≤ ∑ i ∈ Finset.range N, ‖dyadicOperator^i‖ :=
      Finset.single_le_sum (f := fun i => ‖dyadicOperator^i‖) (fun i _ => norm_nonneg (dyadicOperator^i)) (Finset.mem_range.mpr (lt_of_not_ge hn))
    have hs : ‖dyadicOperator^n‖ ≤ C := by dsimp [C]; linarith
    exact hs.trans (le_mul_of_one_le_right (by positivity : 0 ≤ C) hpos)

lemma dyadicScale_for_radius {r : ℝ} (hr0 : 1/2 ≤ r) (hr : r < 1) :
    ∃ n : ℕ, dyadicHeight n ≤ 1-r ∧ 1-r ≤ 2*dyadicHeight n := by
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (show 0 < 1-r by linarith) (show 1-r ≤ 1 by linarith)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨n+1,hlo.le,?_⟩
  change 1-r ≤ 2*((1/2:ℝ)^(n+1))
  rw [pow_succ]
  nlinarith

lemma dyadicHeight_neg_rpow_le {b d : ℝ} (hb : 0 ≤ b) (hd : 0 < d) (n : ℕ)
    (hhi : d ≤ 2*dyadicHeight n) :
    (dyadicHeight n)^(-b) ≤ (2:ℝ)^b * d^(-b) := by
  have hlow : d/2 ≤ dyadicHeight n := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos (show 0 < d/2 by positivity) hlow (neg_nonpos.mpr hb)
  refine hh.trans_eq ?_
  rw [Real.div_rpow hd.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  simp only [div_inv_eq_mul,mul_comm]

lemma family_uniform_mean_bound {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : DiskFamily) (r : ℝ), 1/2 ≤ r → r < 1 →
      (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ C * (1-r)^(-b) := by
  obtain ⟨A,hA,hAc⟩ := whole_circle_dyadic_operator_bound
  obtain ⟨B,hB,hBc⟩ := dyadic_norm_power_bound hb
  have hb0 : 0 ≤ b := dyadicExponent_nonneg.trans hb.le
  refine ⟨A*B*(2:ℝ)^b,by positivity,?_⟩
  intro f r hr0 hr
  obtain ⟨n,hlo,hhi⟩ := dyadicScale_for_radius hr0 hr
  calc
    (∫ t in -Real.pi..Real.pi, circleInverseDensity f r t) ≤ A*‖dyadicOperator^n‖ := hAc f r n hr0 hr hlo hhi
    _ ≤ A*(B*(dyadicHeight n)^(-b)) := mul_le_mul_of_nonneg_left (hBc n) hA.le
    _ = (A*B)*(dyadicHeight n)^(-b) := by ring
    _ ≤ (A*B)*((2:ℝ)^b*(1-r)^(-b)) := mul_le_mul_of_nonneg_left
      (dyadicHeight_neg_rpow_le hb0 (by linarith) n hhi) (by positivity)
    _ = _ := by ring

def normalizedDiskMap (f : ℂ → ℂ) (hf : NormalizedUnivalent f) : C(UnitDisk,ℂ) :=
  ⟨fun z => f z,hf.1.continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)⟩

lemma normalizedDiskMap_extension (f : ℂ → ℂ) (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ disk) : diskExtension (normalizedDiskMap f hf) z = f z := by
  have hz' : z ∈ Metric.ball (0:ℂ) 1 := hz
  simp only [diskExtension,dite_eq_left hz',normalizedDiskMap,ContinuousMap.coe_mk]

lemma normalizedDiskMap_deriv (f : ℂ → ℂ) (hf : NormalizedUnivalent f) {z : ℂ}
    (hz : z ∈ disk) : deriv (diskExtension (normalizedDiskMap f hf)) z = deriv f z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  exact normalizedDiskMap_extension f hf hw

def normalizedDiskFamily (f : ℂ → ℂ) (hf : NormalizedUnivalent f) : DiskFamily :=
  ⟨normalizedDiskMap f hf, by
    refine ⟨hf.1.congr (fun z hz => normalizedDiskMap_extension f hf hz),?_,?_,?_⟩
    · intro z hz w hw he
      exact hf.2.1 hz hw (by simpa only [normalizedDiskMap_extension f hf hz,
        normalizedDiskMap_extension f hf hw] using he)
    · rw [normalizedDiskMap_extension f hf (mem_ball_self zero_lt_one),hf.2.2.1]
    · rw [normalizedDiskMap_deriv f hf (mem_ball_self zero_lt_one),hf.2.2.2]⟩

lemma integralMean_neg_one_as_family (f : ℂ → ℂ) (hf : NormalizedUnivalent f)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    integralMean (-1) f r = (2*Real.pi)⁻¹ *
      ∫ t in -Real.pi..Real.pi, circleInverseDensity (normalizedDiskFamily f hf) r t := by
  unfold integralMean circleInverseDensity
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Real.rpow_neg_one]
  change ‖deriv f _‖⁻¹ = ‖deriv (diskExtension (normalizedDiskMap f hf)) _‖⁻¹
  rw [normalizedDiskMap_deriv f hf (circlePoint_mem_disk hr0 hr t)]

theorem uniform_integralMean_bound_above_dyadicExponent {b : ℝ} (hb : dyadicExponent < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
      ∀ r : ℝ, 1/2 ≤ r → r < 1 → integralMean (-1) f r ≤ C*(1-r)^(-b) := by
  obtain ⟨A,hA,hAc⟩ := family_uniform_mean_bound hb
  refine ⟨(2*Real.pi)⁻¹*A,by positivity,?_⟩
  intro f hf r hr0 hr
  rw [integralMean_neg_one_as_family f hf (by linarith) hr]
  have hh := mul_le_mul_of_nonneg_left (hAc (normalizedDiskFamily f hf) r hr0 hr)
    (show 0 ≤ (2*Real.pi)⁻¹ by positivity)
  simpa only [mul_assoc] using hh

end
end StrictInverseFirstPower

end

end OAI
