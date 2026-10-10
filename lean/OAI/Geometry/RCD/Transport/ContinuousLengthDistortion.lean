import OAI.Geometry.RCD.Transport.ReducedDistanceLimit

namespace OAI

/-! # Continuous bounded reduced distortion on nonnegative lengths -/

open Set Filter TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem sigma_nonpos_le_time {K N t d : ℝ} (hK : K≤0) (hN : 1<N)
    (ht : 0≤t) (ht1 : t≤1) (hd : 0≤d) : sigma K N t d≤ENNReal.ofReal t := by
  by_cases hd0 : d=0
  · simp [sigma,hd0]
  by_cases hK0 : K=0
  · simp [sigma,hK0]
  have hkn := lt_of_le_of_ne hK hK0
  have hdp := lt_of_le_of_ne hd (Ne.symm hd0)
  rw [sigma_neg_eq hkn hN hdp]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_assoc] using sinh_radial_ratio_le_time ht ht1
    (mul_pos hdp (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hkn) (sub_pos.mpr hN))))

theorem sigma_nonpos_length_tendsto_nonneg {K N t d : ℝ} (hK : K≤0) (hN : 1<N)
    (ht : 0≤t) (ht1 : t≤1) (hd : 0≤d) {D : ℕ → ℝ}
    (hD : ∀ j, 0≤D j) (hlim : Tendsto D atTop (𝓝 d)) :
    Tendsto (fun j => sigma K N t (D j)) atTop (𝓝 (sigma K N t d)) := by
  by_cases hK0 : K=0
  · simpa only [hK0,sigma,or_true,ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ENNReal.ofReal t) atTop (𝓝 (ENNReal.ofReal t)))
  have hkn := lt_of_le_of_ne hK hK0
  let a := Real.sqrt (-K/(N-1))
  have ha : 0<a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hkn) (sub_pos.mpr hN))
  by_cases hd0 : d=0
  · let G := fun x : ℝ => ENNReal.ofReal (t*Real.exp (((t*(x*a))^2-(x*a)^2)/6))
    have hG : Continuous G := ENNReal.continuous_ofReal.comp (by fun_prop)
    have hl : Tendsto (fun j => G (D j)) atTop (𝓝 (ENNReal.ofReal t)) := by
      simpa only [G,hd0,zero_mul,mul_zero,zero_pow (by decide : 2≠0),sub_self,zero_div,
        Real.exp_zero,mul_one,Function.comp_def] using hG.continuousAt.tendsto.comp hlim
    have hlo (j) : G (D j) ≤ sigma K N t (D j) := by
      by_cases hj : D j=0
      · simp [G,hj,sigma]
      have hjp : 0<D j := lt_of_le_of_ne (hD j) (Ne.symm hj)
      rw [sigma_neg_eq hkn hN hjp]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using sinh_mul_sharp_gaussian_lower (mul_pos hjp ha) ht ht1
    have hh := tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo
      (fun j => sigma_nonpos_le_time hK hN ht ht1 (hD j))
    simpa only [hd0,sigma,true_or,ite_true] using hh
  · have hdp : 0<d := lt_of_le_of_ne hd (Ne.symm hd0)
    let F := fun x : ℝ => Real.sinh (t*x*a)/Real.sinh (x*a)
    have hF : ContinuousAt F d := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact (Real.sinh_pos_iff.mpr (mul_pos hdp ha)).ne'
    have hpos := hlim.eventually (lt_mem_nhds hdp)
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hF.tendsto.comp hlim)
    rw [sigma_neg_eq hkn hN hdp]
    apply hh.congr'
    filter_upwards [hpos] with j hj
    exact (sigma_neg_eq hkn hN hj t).symm

theorem continuous_sigma_nonpos_length {K N t : ℝ} (hK : K≤0) (hN : 1<N)
    (ht : 0≤t) (ht1 : t≤1) : Continuous (fun d : ℝ≥0 => sigma K N t d) := by
  apply continuous_iff_seqContinuous.mpr
  intro D d hlim
  exact sigma_nonpos_length_tendsto_nonneg hK hN ht ht1 d.property
    (fun j => (D j).property) (NNReal.continuous_coe.continuousAt.tendsto.comp hlim)

end RegularPointCoordinates

end

end OAI
