import OAI.Analysis.NumericalRange.PoissonBoundary

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma circleAverage_pos_at_I {g : ℂ → ℝ} (hg : ContinuousOn g (sphere 0 1))
    (hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ g z) (hI : 0 < g I) :
    0 < Real.circleAverage g 0 1 := by
  unfold Real.circleAverage
  apply smul_pos (by positivity)
  apply intervalIntegral.integral_pos Real.two_pi_pos
  · apply hg.comp (continuous_circleMap 0 1).continuousOn
    intro θ _
    simp
  · intro θ _
    apply hpos
    simp
  · refine ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    simpa [circleMap_pi_div_two] using hI

def herglotzExtension (f : ℂ → ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage (fun t => herglotzRieszKernel 0 w t • (f t : ℂ)) 0 1

lemma analyticOnNhd_herglotzExtension {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1)) :
    AnalyticOnNhd ℂ (herglotzExtension f) (ball 0 1) :=
  (analyticOnNhd_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))).mono
    (by intro z hz; simpa using ne_of_lt (show ‖z‖ < 1 by simpa using hz))

lemma re_herglotzExtension {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 1))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (herglotzExtension f w).re = poissonExtension f w := by
  have hh := re_circleAverage_herglotzRieszKernel_smul
    (hf.circleIntegrable (by norm_num))
    (by simpa using ne_of_lt (show ‖w‖ < 1 by simpa using hw))
  simpa [herglotzExtension, poissonExtension, poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_apply, smul_eq_mul, Pi.mul_def, Function.comp_def] using hh

lemma hasDerivAt_herglotzExtension_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    HasDerivAt (herglotzExtension f)
      (Real.circleAverage (fun t => (2 * conj t) * (f t : ℂ)) 0 1) 0 := by
  have hh := hasDerivAt_circleAverage_herglotzRieszKernel_smul
    ((Complex.continuous_ofReal.comp_continuousOn hf).circleIntegrable (by norm_num))
    (show (0 : ℂ) ∉ sphere 0 |(1 : ℝ)| by simp)
  apply hh.congr_deriv
  symm
  apply Real.circleAverage_congr_sphere
  intro t ht
  have hn : ‖t‖ = 1 := by simpa using ht
  have ht0 : t ≠ 0 := by intro h; simp [h] at hn
  change (2 * conj t) * (f t : ℂ) = (2 * t / (t - 0) ^ 2) • (f t : ℂ)
  rw [← Complex.inv_eq_conj hn]
  simp only [sub_zero, smul_eq_mul]
  congr 1
  field_simp

lemma im_deriv_herglotzExtension_zero {f : ℂ → ℝ}
    (hf : ContinuousOn f (sphere 0 1)) :
    (deriv (herglotzExtension f) 0).im =
      Real.circleAverage (fun t => -2 * t.im * f t) 0 1 := by
  rw [(hasDerivAt_herglotzExtension_zero hf).deriv]
  have hi : CircleIntegrable (fun t => (2 * conj t) * (f t : ℂ)) 0 1 := by
    exact ((continuous_const.mul Complex.continuous_conj).continuousOn.mul
      (Complex.continuous_ofReal.comp_continuousOn hf)).circleIntegrable (by norm_num)
  have he := Complex.imCLM.circleAverage_comp_comm hi
  change Complex.imCLM (Real.circleAverage (fun t => (2 * conj t) * (f t : ℂ)) 0 1) = _
  rw [← he]
  apply Real.circleAverage_congr_sphere
  intro t _
  simp [Complex.mul_im, mul_assoc]

theorem herglotz_oddBoundary_deriv_ne_zero {u : ℂ → ℝ}
    (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0) :
    deriv (herglotzExtension (oddBoundary u)) 0 ≠ 0 := by
  have hf := continuousOn_oddBoundary huc hzero
  have hn : ∀ t ∈ sphere (0 : ℂ) 1, 0 ≤ -2 * t.im * oddBoundary u t := by
    intro t ht
    by_cases hp : 0 ≤ t.im
    · rw [oddBoundary, ite_eq_left hp]
      by_cases he : t.im = 0
      · simp [he]
      · have hh := hneg t ht (lt_of_le_of_ne hp (Ne.symm he))
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hh.le
    · rw [oddBoundary, ite_eq_right hp]
      have hh := hneg (conj t) (by simpa using ht) (by simp; linarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hp : 0 < Real.circleAverage (fun t => -2 * t.im * oddBoundary u t) 0 1 := by
    apply circleAverage_pos_at_I
      ((continuous_const.mul Complex.continuous_im).continuousOn.mul hf) hn
    have hi : u I < 0 := hneg I (by simp) (by simp)
    change 0 < -2 * I.im * oddBoundary u I
    simp only [oddBoundary, Complex.I_im, show (0 : ℝ) ≤ 1 by norm_num, ite_true]
    linarith
  rw [← im_deriv_herglotzExtension_zero hf] at hp
  intro he
  simp [he] at hp

theorem holomorphic_reflection_modulus {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u upperDisk) (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (ball 0 1) ∧
      (∀ z, F z ≠ 0) ∧ deriv F 0 ≠ 0 ∧
      (∀ z ∈ upperDisk, ‖F z‖ = Real.exp (u z)) := by
  let f := oddBoundary u
  let H := herglotzExtension f
  have hf : ContinuousOn f (sphere 0 1) := continuousOn_oddBoundary huc hzero
  have hH : AnalyticOnNhd ℂ H (ball 0 1) := analyticOnNhd_herglotzExtension hf
  have hEq : EqOn (diskDirichlet f) u (closure upperDisk) := by
    apply harmonic_eqOn_closure_of_eqOn_frontier
      (isBounded_ball.subset inter_subset_left)
      ((harmonicOnNhd_diskDirichlet hf).mono inter_subset_left) hu
      ((continuousOn_diskDirichlet hf).mono (closure_upperDisk_subset.trans inter_subset_left))
      (huc.mono closure_upperDisk_subset)
    intro z hz
    have hc := closure_upperDisk_subset hz.1
    rcases upper_frontier_or hz with hn | hi
    · rw [diskDirichlet_eq_boundary (by simpa using hn)]
      exact ite_eq_left hc.2
    · have hn : ‖z‖ ≤ 1 := by simpa using hc.1
      by_cases he : ‖z‖ = 1
      · rw [diskDirichlet_eq_boundary (by simpa using he)]
        exact ite_eq_left hc.2
      · rw [diskDirichlet_zero_real (fun _ hz => oddBoundary_odd hzero hz)
          (lt_of_le_of_ne hn he) hi, hzero z hc hi]
  refine ⟨fun z => Complex.exp (H z), ?_, fun z => Complex.exp_ne_zero _, ?_, ?_⟩
  · intro z hz
    exact analyticAt_cexp.comp (hH z hz)
  · have hh := (Complex.hasDerivAt_exp (H 0)).comp 0
      ((hH 0 (by simp)).differentiableAt.hasDerivAt)
    change deriv (Complex.exp ∘ H) 0 ≠ 0
    rw [hh.deriv]
    exact mul_ne_zero (Complex.exp_ne_zero _) (herglotz_oddBoundary_deriv_ne_zero huc hzero hneg)
  · intro z hz
    rw [Complex.norm_exp, re_herglotzExtension hf hz.1]
    have hh := hEq (subset_closure hz)
    simpa [diskDirichlet, show ‖z‖ < 1 by simpa using hz.1] using congrArg Real.exp hh

theorem holomorphic_reflection_upperDisk {g : ℂ → ℂ} {u : ℂ → ℝ}
    (hg : AnalyticOnNhd ℂ g upperDisk)
    (hu : HarmonicOnNhd u upperDisk) (huc : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    (hneg : ∀ z ∈ sphere (0 : ℂ) 1, 0 < z.im → u z < 0)
    (hmod : ∀ z ∈ upperDisk, ‖g z‖ = Real.exp (u z)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧
      (∀ z, G z ≠ 0) ∧ deriv G 0 ≠ 0 ∧ EqOn G g upperDisk := by
  obtain ⟨F,hFa,hFn,hFd,hFm⟩ := holomorphic_reflection_modulus hu huc hzero hneg
  let q : ℂ → ℂ := fun z => g z / F z
  have hqa : AnalyticOnNhd ℂ q upperDisk := fun z hz => (hg z hz).div (hFa z hz.1) (hFn z)
  have hqn : ∀ z ∈ upperDisk, ‖q z‖ = 1 := by
    intro z hz
    simp only [q, norm_div, hmod z hz, hFm z hz, div_self (Real.exp_ne_zero _)]
  let p : ℂ := (1/2 : ℝ) • I
  have hp : p ∈ upperDisk := by
    constructor
    · norm_num [p, mem_ball, dist_zero_right, norm_smul]
    · simp [p]
  have hc : IsPreconnected upperDisk := by
    exact ((convex_ball (0 : ℂ) 1).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc upperDisk_isOpen
    hqa.differentiableOn hp (show IsMaxOn (norm ∘ q) upperDisk p from
      fun z hz => by simp [hqn z hz, hqn p hp])
  have hqp : q p ≠ 0 := norm_ne_zero_iff.mp (by rw [hqn p hp]; norm_num)
  refine ⟨fun z => q p * F z, ?_, fun z => mul_ne_zero hqp (hFn z), ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hFa z hz)
  · have hd := ((hFa 0 (by simp)).differentiableAt.hasDerivAt).const_mul (q p)
    rw [hd.deriv]
    exact mul_ne_zero hqp hFd
  · intro z hz
    have he : q z = q p := hconst hz
    rw [← he]
    exact div_mul_cancel₀ _ (hFn z)


open Set Filter Metric Complex
open scoped Topology

def upperLogNorm (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  if z.im = 0 then 0 else Real.log ‖g z‖

lemma upperLogNorm_eventuallyEq (g : ℂ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    upperLogNorm g =ᶠ[𝓝 z] (fun w => Real.log ‖g w‖) := by
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hz] with w hw
  exact ite_eq_right hw

lemma upperLogNorm_continuousOn {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ g z)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → g z ≠ 0)
    (hb : ∀ p ∈ upperClosedDisk, p.im = 0 →
      Tendsto (fun z => ‖g z‖) (𝓝[{z : ℂ | 0 < z.im}] p) (𝓝 1)) :
    ContinuousOn (upperLogNorm g) upperClosedDisk := by
  intro p hp
  by_cases hz : p.im = 0
  · have hpos : ContinuousWithinAt (upperLogNorm g) {z : ℂ | 0 < z.im} p := by
      change Tendsto (upperLogNorm g) _ (𝓝 (upperLogNorm g p))
      rw [upperLogNorm, ite_eq_left hz]
      have ht := (hb p hp hz).log (by norm_num : (1 : ℝ) ≠ 0)
      rw [Real.log_one] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (ite_eq_right (ne_of_gt hz)).symm
    have hreal : ContinuousWithinAt (upperLogNorm g) {z : ℂ | z.im = 0} p := by
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr
      · intro z hz
        exact ite_eq_left hz
      · exact ite_eq_left hz
    apply (hreal.union hpos).mono
    intro z hz
    by_cases he : z.im = 0
    · exact Or.inl he
    · exact Or.inr (lt_of_le_of_ne hz.2 (Ne.symm he))
  · have hp' : 0 < p.im := lt_of_le_of_ne hp.2 (Ne.symm hz)
    have hc := ((hg p hp hp').continuousAt.norm.log (norm_ne_zero_iff.mpr (hn p hp hp')))
    exact (hc.congr (upperLogNorm_eventuallyEq g hz).symm).continuousWithinAt

theorem conformal_reflection_upperDisk {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ g z)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → g z ≠ 0)
    (hsmall : ∀ z ∈ upperClosedDisk, 0 < z.im → ‖g z‖ < 1)
    (hb : ∀ p ∈ upperClosedDisk, p.im = 0 →
      Tendsto (fun z => ‖g z‖) (𝓝[{z : ℂ | 0 < z.im}] p) (𝓝 1)) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (ball 0 1) ∧
      (∀ z, G z ≠ 0) ∧ deriv G 0 ≠ 0 ∧ EqOn G g upperDisk := by
  have hsub : upperDisk ⊆ upperClosedDisk := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, show (0 : ℝ) ≤ z.im from hz.2.le⟩
  apply holomorphic_reflection_upperDisk (u := upperLogNorm g)
  · exact fun z hz => hg z (hsub hz) hz.2
  · intro z hz
    rw [harmonicAt_congr_nhds (upperLogNorm_eventuallyEq g (ne_of_gt hz.2))]
    exact (hg z (hsub hz) hz.2).harmonicAt_log_norm (hn z (hsub hz) hz.2)
  · exact upperLogNorm_continuousOn hg hn hb
  · intro z _ hz
    exact ite_eq_left hz
  · intro z hz him
    rw [upperLogNorm, ite_eq_right (ne_of_gt him)]
    have hc : z ∈ upperClosedDisk := ⟨sphere_subset_closedBall hz,him.le⟩
    exact Real.log_neg (norm_pos_iff.mpr (hn z hc him)) (hsmall z hc him)
  · intro z hz
    rw [upperLogNorm, ite_eq_right (ne_of_gt hz.2),
      Real.exp_log (norm_pos_iff.mpr (hn z (hsub hz) hz.2))]

end

open Set Filter Metric
open scoped Topology

theorem compact_local_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hcont : ∀ z ∈ K, ContinuousAt f z) (hinj : InjOn f K)
    (hloc : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn f U) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  let R : Set (ℂ × ℂ) := {p | f p.1 = f p.2 → p.1 = p.2}
  have hR : R ∈ 𝓝ˢ (K ×ˢ K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases hxy : x = y
    · subst y
      obtain ⟨U,hU,hUi⟩ := hloc x hx
      apply mem_of_superset (show U ×ˢ U ∈ 𝓝 (x,x) by
        rw [nhds_prod_eq]; exact prod_mem_prod hU hU)
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      exact hUi ha hb
    · have hne : f x - f y ≠ 0 := sub_ne_zero.mpr (fun he => hxy (hinj hx hy he))
      have hc : ContinuousAt (fun p : ℂ × ℂ => f p.1 - f p.2) (x,y) :=
        ((hcont x hx).comp continuousAt_fst).sub ((hcont y hy).comp continuousAt_snd)
      filter_upwards [hc.eventually_ne hne] with p hp
      exact fun he => False.elim (hp (sub_eq_zero.mpr he))
  rw [hK.nhdsSet_prod_eq hK, mem_prod_self_iff] at hR
  obtain ⟨V,hV,hVR⟩ := hR
  obtain ⟨U,hU,hKU,hUV⟩ := mem_nhdsSet_iff_exists.mp hV
  refine ⟨U,hU,hKU,?_⟩
  intro x hx y hy he
  have hr := hVR (show (x,y) ∈ V ×ˢ V from ⟨hUV hx,hUV hy⟩)
  exact hr he

theorem analytic_compact_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (ha : AnalyticOnNhd ℂ f K) (hd : ∀ z ∈ K, deriv f z ≠ 0)
    (hi : InjOn f K) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U ∧ AnalyticOnNhd ℂ f U := by
  obtain ⟨U,hU,hKU,hUi⟩ := compact_local_injective_collar hK
    (fun z hz => (ha z hz).continuousAt) hi (by
      intro z hz
      have he := (ha z hz).hasStrictDerivAt.eventually_left_inverse (hd z hz)
      refine ⟨_,he,?_⟩
      intro x hx y hy hxy
      rw [← hx, ← hy, hxy])
  let W := {z | AnalyticAt ℂ f z}
  have hW : IsOpen W := isOpen_analyticAt ℂ f
  refine ⟨U ∩ W,hU.inter hW,fun z hz => ⟨hKU hz,ha z hz⟩,
    hUi.mono inter_subset_left,fun z hz => hz.2⟩

theorem conformal_modulus_boundary {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : MapsTo f U (ball 0 1)) (hg : ContinuousOn g (ball 0 1))
    (hgU : MapsTo g (ball 0 1) U) (hgf : ∀ z ∈ U, g (f z) = z)
    {p : ℂ} (hp : p ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,hr,hra⟩ := exists_between (max_lt ha (by norm_num : (0:ℝ) < 1))
    have har : a < r := lt_of_le_of_lt (le_max_left a 0) hr
    have hsub : closedBall (0:ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hra
    have hK : IsCompact (g '' closedBall (0:ℂ) r) :=
      (isCompact_closedBall 0 r).image_of_continuousOn (hg.mono hsub)
    have hpU : p ∉ U := by
      rw [hU.frontier_eq] at hp
      exact hp.2
    have hpK : p ∉ g '' closedBall (0:ℂ) r := fun ⟨z,hz,he⟩ => hpU (he ▸ hgU (hsub hz))
    have hn : (g '' closedBall (0:ℂ) r)ᶜ ∈ 𝓝 p := hK.isClosed.isOpen_compl.mem_nhds hpK
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with z hz hzK
    have hnz : r < ‖f z‖ := by
      by_contra h
      have hfz : f z ∈ closedBall (0:ℂ) r := by simpa using le_of_not_gt h
      exact hzK ⟨f z,hfz,hgf z hz⟩
    exact har.trans hnz
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf hz)).trans hb


end CompleteCrouzeix

end

end OAI
