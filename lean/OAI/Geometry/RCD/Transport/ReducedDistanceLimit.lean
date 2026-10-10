import OAI.Geometry.RCD.Transport.MidpointLengthApproximation

namespace OAI

/-! # Distance continuity of reduced distortion, including zero length

At zero length the sharp Gaussian lower bound and the linear upper bound
squeeze the hyperbolic ratio to its continuous value.
-/

open Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RegularPointCoordinates

theorem sigma_nonpos_ne_top {K N t d : ℝ} (hK : K≤0) (hN : 1<N) (hd : 0≤d) :
    sigma K N t d≠∞ := by
  by_cases hd0 : d=0
  · simp [sigma,hd0]
  by_cases hK0 : K=0
  · simp [sigma,hK0]
  rw [sigma_neg_eq (lt_of_le_of_ne hK hK0) hN (lt_of_le_of_ne hd (Ne.symm hd0))]
  exact ENNReal.ofReal_ne_top

theorem sigma_nonpos_ne_zero {K N t d : ℝ} (hK : K≤0) (hN : 1<N)
    (ht : 0<t) (hd : 0≤d) : sigma K N t d≠0 := by
  by_cases hd0 : d=0
  · simpa [sigma,hd0] using (ENNReal.ofReal_pos.mpr ht).ne'
  by_cases hK0 : K=0
  · simpa [sigma,hK0] using (ENNReal.ofReal_pos.mpr ht).ne'
  have hKneg := lt_of_le_of_ne hK hK0
  have hdpos := lt_of_le_of_ne hd (Ne.symm hd0)
  rw [sigma_neg_eq hKneg hN hdpos]
  apply (ENNReal.ofReal_pos.mpr _).ne'
  apply div_pos
  · exact Real.sinh_pos_iff.mpr (mul_pos (mul_pos ht hdpos)
      (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hN))))
  · exact Real.sinh_pos_iff.mpr (mul_pos hdpos
      (Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hN))))

theorem sigma_nonpos_length_tendsto {K N t d : ℝ} (hK : K≤0) (hN : 1<N)
    (ht : 0<t) (ht1 : t≤1) (hd : 0≤d) {D : ℕ → ℝ}
    (hD : ∀ m, 0<D m) (hlim : Tendsto D atTop (𝓝 d)) :
    Tendsto (fun m => sigma K N t (D m)) atTop (𝓝 (sigma K N t d)) := by
  by_cases hK0 : K=0
  · simpa only [hK0,sigma,or_true,ite_true] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ENNReal.ofReal t) atTop (𝓝 (ENNReal.ofReal t)))
  have hKneg := lt_of_le_of_ne hK hK0
  let a := Real.sqrt (-K/(N-1))
  have ha : 0<a := Real.sqrt_pos.mpr (div_pos (neg_pos.mpr hKneg) (sub_pos.mpr hN))
  let F := fun x : ℝ => Real.sinh (t*x*a)/Real.sinh (x*a)
  have he (m) : sigma K N t (D m)=ENNReal.ofReal (F (D m)) :=
    sigma_neg_eq hKneg hN (hD m) t
  simp_rw [he]
  by_cases hd0 : d=0
  · have hl : Tendsto (fun m => t*Real.exp (((t*(D m*a))^2-(D m*a)^2)/6)) atTop (𝓝 t) := by
      have hh : Continuous (fun x : ℝ => t*Real.exp (((t*(x*a))^2-(x*a)^2)/6)) := by fun_prop
      simpa [hd0,Function.comp_def] using hh.continuousAt.tendsto.comp hlim
    have hf : Tendsto (fun m => F (D m)) atTop (𝓝 t) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
      · intro m
        simpa only [F,mul_assoc] using sinh_mul_sharp_gaussian_lower (mul_pos (hD m) ha) ht.le ht1
      · intro m
        simpa only [F,mul_assoc] using sinh_radial_ratio_le_time ht.le ht1 (mul_pos (hD m) ha)
    simpa only [hd0,sigma,zero_mul,true_or,ite_true,Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto t |>.comp hf
  · have hdpos : 0<d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hF : ContinuousAt F d := by
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact (Real.sinh_pos_iff.mpr (mul_pos hdpos ha)).ne'
    rw [sigma_neg_eq hKneg hN hdpos]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hF.tendsto.comp hlim)

end RegularPointCoordinates

end OAI
