import OAI.Probability.SLE.Loewner.UnivalentRootFactor
import OAI.Probability.SLE.Geometry.RootCoefficientBound

namespace OAI

/-! The sharp second-coefficient estimate for disk-univalent functions,
obtained from the actual odd-root exterior map and its area inequality. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma second_derivative_eq_twice_dslope {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hf0 : f 0=0) :
    deriv (deriv f) 0=2*deriv (dslope f 0) 0 := by
  let g := dslope f 0
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) zero_lt_one)).mpr hf
  have he (z : ℂ) : f z=z*g z := by
    have h := sub_smul_dslope f 0 z
    simpa only [sub_zero,hf0,smul_eq_mul] using h.symm
  have hD : deriv f =ᶠ[𝓝 (0:ℂ)] (fun z => g z+z*deriv g z) := by
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
    have hd := (hasDerivAt_id z).mul ((hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt)
    have hd' := hd.congr_of_eventuallyEq (Eventually.of_forall he)
    simpa only [id_eq,one_mul] using hd'.deriv
  have hga := hg.analyticAt (ball_mem_nhds (0:ℂ) zero_lt_one)
  have hd := hga.differentiableAt.hasDerivAt.add
    ((hasDerivAt_id (0:ℂ)).mul hga.deriv.differentiableAt.hasDerivAt)
  have hh := (hd.congr_of_eventuallyEq hD).deriv
  simpa only [id_eq,one_mul,zero_mul,add_zero,two_mul,g] using hh

lemma normalized_univalent_second_derivative {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hf0 : f 0=0) (hd0 : deriv f 0=1) :
    ‖deriv (deriv f) 0‖≤4 := by
  obtain ⟨q,hq,hq0,hq2,hqne,hqi⟩ := univalent_root_factor hf hi hf0 hd0
  have hqb := root_factor_derivative_le_one hq hq0 hqne hqi
  have hqD := (hq.differentiableAt (ball_mem_nhds (0:ℂ) zero_lt_one)).hasDerivAt
  have he : dslope f 0 =ᶠ[𝓝 (0:ℂ)] (fun z => q z^2) := by
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
    exact (hq2 z hz).symm
  have hgD := ((hqD.pow 2).congr_of_eventuallyEq he).deriv
  have hg : deriv (dslope f 0) 0=2*deriv q 0 := by simpa [hq0] using hgD
  have h4 : deriv (deriv f) 0=4*deriv q 0 := by
    rw [second_derivative_eq_twice_dslope hf hf0,hg]
    ring
  rw [h4,norm_mul]
  norm_num
  linarith

theorem univalent_second_derivative_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1)) :
    ‖deriv (deriv f) 0‖≤4*‖deriv f 0‖ := by
  have hzero : (0:ℂ)∈ball 0 1 := mem_ball_self zero_lt_one
  have hd : deriv f 0≠0 := univalent_deriv_ne_zero isOpen_ball hf hi hzero
  let P (z : ℂ) := (f z-f 0)/deriv f 0
  have hP : DifferentiableOn ℂ P (ball 0 1) := (hf.sub_const _).div_const _
  have hPi : InjOn P (ball 0 1) := by
    intro z hz w hw he
    apply hi hz hw
    have hh := (div_left_inj' hd).mp he
    linear_combination hh
  have hP0 : P 0=0 := by simp [P]
  have hPD (z : ℂ) (hz : z∈ball (0:ℂ) 1) : deriv P z=deriv f z/deriv f 0 := by
    exact (((hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const _).div_const _).deriv
  have hP1 : deriv P 0=1 := by rw [hPD 0 hzero,div_self hd]
  have hfA := hf.analyticAt (isOpen_ball.mem_nhds hzero)
  have hP2 : deriv (deriv P) 0=deriv (deriv f) 0/deriv f 0 := by
    have hh := hfA.deriv.differentiableAt.hasDerivAt.div_const (deriv f 0)
    exact (hh.congr_of_eventuallyEq (by
      filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with z hz
      exact hPD z hz)).deriv
  have hh := normalized_univalent_second_derivative hP hPi hP0 hP1
  rw [hP2,norm_div] at hh
  exact (div_le_iff₀ (norm_pos_iff.mpr hd)).mp hh

end SLEExactGauge

end

end OAI
