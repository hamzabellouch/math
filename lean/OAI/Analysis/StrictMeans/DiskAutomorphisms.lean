import OAI.Analysis.StrictMeans.RootTransform

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower

noncomputable section

lemma not_eventually_constant_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) :
    ¬ ∀ᶠ w in 𝓝 z, f w = f z := by
  intro h
  have hz := mem_of_mem_nhds hs
  have hh : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds hs,
      eventually_mem_nhdsWithin] with w hw hws hwz
    exact hwz (hi hws hz hw)
  exact Filter.Eventually.exists hh |>.elim (fun _ h => h)

lemma analytic_injOn_map_nhds {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    map f (𝓝 z) = 𝓝 (f z) := by
  exact le_antisymm hf.continuousAt
    (hf.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hs hi))

lemma invFunOn_continuousAt {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : s ∈ 𝓝 z) (hi : InjOn f s) (hf : AnalyticAt ℂ f z) :
    ContinuousAt (invFunOn f s) (f z) := by
  have hz := mem_of_mem_nhds hs
  rw [ContinuousAt, hi.leftInvOn_invFunOn hz, ← analytic_injOn_map_nhds hs hi hf]
  change map (invFunOn f s) (map f (𝓝 z)) ≤ 𝓝 z
  rw [Filter.map_map]
  have hh : (invFunOn f s ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs] with w hw
    exact hi.leftInvOn_invFunOn hw
  exact (tendsto_congr' hh).mpr tendsto_id

lemma deriv_eventually_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    ∀ᶠ w in 𝓝[≠] z, deriv f w ≠ 0 := by
  have hfa : AnalyticAt ℂ (deriv f) z := (hf.deriv hs).analyticAt (hs.mem_nhds hz)
  refine hfa.eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
  intro hzero
  have he : ∀ᶠ w in 𝓝 z, w ∈ s ∧ deriv f w = 0 :=
    Filter.Eventually.and (hs.mem_nhds hz) hzero
  obtain ⟨r, hr, hrsub⟩ := Metric.eventually_nhds_iff.mp he
  have hdiff : DifferentiableOn ℂ f (ball z r) := hf.mono (fun w hw => (hrsub hw).1)
  have hc : ∀ᶠ w in 𝓝 z, f w = f z := by
    filter_upwards [ball_mem_nhds z hr] with w hw
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected hdiff
      (fun w hw => (hrsub hw).2) hw (mem_ball_self hr)
  exact not_eventually_constant_of_injOn (hs.mem_nhds hz) hi hc

theorem deriv_ne_zero_of_injOn {s : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (hs : IsOpen s) (hz : z ∈ s) (hi : InjOn f s) (hf : DifferentiableOn ℂ f s) :
    deriv f z ≠ 0 := by
  let g := invFunOn f s
  have hfa : AnalyticAt ℂ f z := hf.analyticAt (hs.mem_nhds hz)
  have hg : ContinuousAt g (f z) := invFunOn_continuousAt (hs.mem_nhds hz) hi hfa
  have hgz : g (f z) = z := hi.leftInvOn_invFunOn hz
  have himage : f '' s ∈ 𝓝 (f z) := by
    rw [← analytic_injOn_map_nhds (hs.mem_nhds hz) hi hfa]
    exact image_mem_map (hs.mem_nhds hz)
  have hder := deriv_eventually_ne_zero_of_injOn hs hz hi hf
  have hder' : ∀ᶠ w in 𝓝 (f z), g w ≠ z → deriv f (g w) ≠ 0 := by
    have hh := hg.tendsto
    rw [hgz] at hh
    exact hh.eventually (eventually_nhdsWithin_iff.mp hder)
  have hgd : ∀ᶠ w in 𝓝[≠] (f z), DifferentiableAt ℂ g w := by
    filter_upwards [hder'.filter_mono nhdsWithin_le_nhds,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds himage, eventually_mem_nhdsWithin]
      with w hd hw hwz
    have hgw : g w ∈ s := invFunOn_mem hw
    have hfg : f (g w) = w := invFunOn_eq hw
    have hgne : g w ≠ z := by
      intro he
      apply hwz
      change w = f z
      rw [← hfg, he]
    have hleft : ∀ᶠ x in 𝓝 (g w), g (f x) = x := by
      filter_upwards [hs.mem_nhds hgw] with x hx
      exact hi.leftInvOn_invFunOn hx
    have hh := (hf.analyticAt (hs.mem_nhds hgw)).hasStrictDerivAt.to_local_left_inverse
      (hd hgne) hleft
    simpa only [hfg] using hh.hasDerivAt.differentiableAt
  have hga := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hg
  have hcomp := hga.differentiableAt.hasDerivAt.comp z (hf.differentiableAt (hs.mem_nhds hz)).hasDerivAt
  have hleft : (g ∘ f) =ᶠ[𝓝 z] id := by
    filter_upwards [hs.mem_nhds hz] with x hx
    exact hi.leftInvOn_invFunOn hx
  have hid : HasDerivAt (g ∘ f) 1 z := (hasDerivAt_id z).congr_of_eventuallyEq hleft
  have he := hcomp.unique hid
  intro hzero
  simp only [hzero, mul_zero] at he
  exact zero_ne_one he

end
end StrictInverseFirstPower

namespace StrictInverseFirstPower
noncomputable section

lemma second_deriv_eq_twice_dslope {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) :
    deriv (deriv f) 0 = 2 * deriv (dslope f 0) 0 := by
  let u := dslope f 0
  have hu : DifferentiableOn ℂ u (ball 0 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (by simp))).mpr hd
  have he (z : ℂ) : f z = z * u z + f 0 := by
    have hh := sub_smul_dslope f (0 : ℂ) z
    simp only [sub_zero, smul_eq_mul] at hh
    exact (eq_sub_iff_add_eq.mp hh).symm
  have hder : deriv f =ᶠ[𝓝 (0 : ℂ)] (fun z => u z + z * deriv u z) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    have hzU := hu.differentiableAt (isOpen_ball.mem_nhds hz)
    have hp := ((hasDerivAt_id z).mul hzU.hasDerivAt).add_const (f 0)
    have hpf : HasDerivAt f (u z + z * deriv u z) z := by
      convert hp using 1
      all_goals first | rfl | exact funext he | simp
    exact hpf.deriv
  have hu0 := hu.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hu'0 := (hu.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))
  have hp := hu0.hasDerivAt.add ((hasDerivAt_id (0 : ℂ)).mul hu'0.hasDerivAt)
  have hpf : HasDerivAt (deriv f) (2 * deriv u 0) 0 := by
    convert hp.congr_of_eventuallyEq hder using 1
    all_goals first | rfl | simp [two_mul]
  exact hpf.deriv

lemma second_deriv_norm_le_four {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) : ‖deriv (deriv f) 0‖ ≤ 4 := by
  rw [second_deriv_eq_twice_dslope hd, norm_mul]
  have hh := second_coefficient_le_two hd hi h0 h1
  norm_num
  linarith

def diskAutomorphism (a z : ℂ) : ℂ := (a + z) / (1 + conj a * z)

lemma diskAutomorphism_den_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 + conj a * z ≠ 0 := by
  have hl : ‖conj a * z‖ < 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro he
  have he' : conj a * z = -1 := by linear_combination he
  rw [he'] at hl
  norm_num at hl

lemma diskAutomorphism_norm_identity (a z : ℂ) :
    ‖1 + conj a * z‖ ^ 2 - ‖a + z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, mul_im,
    conj_re, conj_im, one_re, one_im]
  ring

lemma diskAutomorphism_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (diskAutomorphism a) (ball 0 1) (ball 0 1) := by
  intro z hz
  simp only [mem_ball, dist_zero_right] at *
  have hn := diskAutomorphism_norm_identity a z
  have hp : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z])
  have hl : ‖a + z‖ < ‖1 + conj a * z‖ := by
    nlinarith [norm_nonneg (a + z), norm_nonneg (1 + conj a * z)]
  dsimp only [diskAutomorphism]
  rw [norm_div, div_lt_one (norm_pos_iff.mpr (diskAutomorphism_den_ne ha hz))]
  exact hl

lemma diskAutomorphism_injOn {a : ℂ} (ha : ‖a‖ < 1) :
    InjOn (diskAutomorphism a) (ball 0 1) := by
  intro z hz w hw he
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have haN : 1 - conj a * a ≠ 0 := by
    rw [← normSq_eq_conj_mul_self, ← ofReal_one, ← ofReal_sub, ne_eq, ofReal_eq_zero]
    rw [normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne ha hz') (diskAutomorphism_den_ne ha hw')).mp he
  have he'' : (1 - conj a * a) * (z - w) = 0 := by linear_combination he'
  exact sub_eq_zero.mp ((mul_eq_zero.mp he'').resolve_left haN)

lemma diskAutomorphism_hasDerivAt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    HasDerivAt (diskAutomorphism a)
      ((1 - conj a * a) / (1 + conj a * z) ^ 2) z := by
  have hh := ((hasDerivAt_id z).const_add a).div
    (((hasDerivAt_id z).const_mul (conj a)).const_add 1) (diskAutomorphism_den_ne ha hz)
  convert hh using 1
  all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (diskAutomorphism a) (ball 0 1) := by
  intro z hz
  exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).differentiableAt.differentiableWithinAt

@[simp] lemma diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by simp [diskAutomorphism]

lemma diskAutomorphism_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (diskAutomorphism a) 0 = 1 - conj a * a := by
  simpa using (diskAutomorphism_hasDerivAt (z := 0) ha (by simp)).deriv

lemma diskAutomorphism_second_deriv_zero {a : ℂ} (ha : ‖a‖ < 1) :
    deriv (deriv (diskAutomorphism a)) 0 = -2 * conj a * (1 - conj a * a) := by
  have he : deriv (diskAutomorphism a) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (1 - conj a * a) / (1 + conj a * z) ^ 2) := by
    filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
    exact (diskAutomorphism_hasDerivAt ha (by simpa [mem_ball, dist_zero_right] using hz)).deriv
  have hn : (1 + conj a * (0 : ℂ)) ^ 2 ≠ 0 := by simp
  have hp := (hasDerivAt_const (0 : ℂ) (1 - conj a * a)).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (conj a)).const_add 1).pow 2) hn
  have hpf : HasDerivAt (deriv (diskAutomorphism a)) (-2 * conj a * (1 - conj a * a)) 0 := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (simp; ring)
  exact hpf.deriv

lemma second_deriv_comp {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f (g z)) (hg : AnalyticAt ℂ g z) :
    deriv (deriv (f ∘ g)) z = deriv (deriv f) (g z) * deriv g z ^ 2 +
      deriv f (g z) * deriv (deriv g) z := by
  have he : deriv (f ∘ g) =ᶠ[𝓝 z] (fun w => deriv f (g w) * deriv g w) := by
    filter_upwards [hg.eventually_analyticAt,
      hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt] with w hgw hfw
    exact deriv_comp w hfw.differentiableAt hgw.differentiableAt
  have hp := (hf.deriv.differentiableAt.hasDerivAt.comp z hg.differentiableAt.hasDerivAt).mul
    hg.deriv.differentiableAt.hasDerivAt
  have hpf : HasDerivAt (deriv (f ∘ g))
      (deriv (deriv f) (g z) * deriv g z ^ 2 + deriv f (g z) * deriv (deriv g) z) z := by
    convert hp.congr_of_eventuallyEq he using 1
    all_goals first | rfl | (dsimp only [id_eq, Function.comp_apply]; ring)
  exact hpf.deriv

end
end StrictInverseFirstPower

end

end OAI
