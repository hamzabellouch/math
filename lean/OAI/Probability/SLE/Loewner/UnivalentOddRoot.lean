import OAI.Probability.SLE.Loewner.UnivalentInverseAnalytic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible

namespace OAI

/-! The normalized odd square-root transform used in the sharp disk
growth argument. The square root is constructed, not assumed. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma hasDerivAt_of_continuous_square_root {g q : ℂ → ℂ} {a d : ℂ}
    (hg : HasDerivAt g d a) (hq : ContinuousAt q a) (hqa : q a≠0)
    (he : ∀ᶠ z in 𝓝 a, q z^2=g z) :
    HasDerivAt q (d/(2*q a)) a := by
  have hea : q a^2=g a := he.self_of_nhds
  have hn : q a+q a≠0 := by simpa only [←two_mul] using mul_ne_zero (by norm_num) hqa
  have hsum : Tendsto (fun z => q z+q a) (𝓝[≠] a) (𝓝 (q a+q a)) :=
    (hq.add_const (q a)).tendsto.mono_left nhdsWithin_le_nhds
  have ht := hg.tendsto_slope.div hsum hn
  have heq : (fun z => slope g a z/(q z+q a)) =ᶠ[𝓝[≠] a] slope q a := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,
      ((hq.add_const (q a)).eventually_ne hn).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hsum hza
    simp only [slope_def_field,←hz,←hea]
    field_simp
    ring
  apply hasDerivAt_iff_tendsto_slope.mpr
  simpa only [←two_mul] using ht.congr' heq

lemma differentiableOn_continuous_square_root {D : Set ℂ} (hD : IsOpen D)
    {g q : ℂ → ℂ} (hg : DifferentiableOn ℂ g D) (hq : ContinuousOn q D)
    (he : ∀ z∈D, q z^2=g z) (hne : ∀ z∈D, g z≠0) :
    DifferentiableOn ℂ q D := by
  intro a ha
  have hqa : q a≠0 := by intro h; apply hne a ha; rw [←he a ha,h,zero_pow (by norm_num)]
  exact (hasDerivAt_of_continuous_square_root (hg.differentiableAt (hD.mem_nhds ha)).hasDerivAt
    ((hq a ha).continuousAt (hD.mem_nhds ha)) hqa
    (by filter_upwards [hD.mem_nhds ha] with z hz; exact he z hz)).differentiableAt.differentiableWithinAt

lemma exists_normalized_analytic_square_root {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hne : ∀ z∈ball (0:ℂ) 1, g z≠0)
    (h0 : g 0=1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q (ball 0 1) ∧ q 0=1 ∧
      ∀ z∈ball (0:ℂ) 1, q z^2=g z := by
  have hb : (ball (0:ℂ) 1).Nonempty := ⟨0,mem_ball_self zero_lt_one⟩
  have hcontract : ContractibleSpace ↥(ball (0:ℂ) 1) :=
    (convex_ball (0:ℂ) 1).contractibleSpace hb
  have hsimply : IsSimplyConnected (ball (0:ℂ) 1) := by
    change SimplyConnectedSpace ↥(ball (0:ℂ) 1)
    infer_instance
  obtain ⟨s,hsc,hs⟩ := Complex.exists_continuousOn_pow_eq hsimply isOpen_ball hg.continuousOn
    (by rintro ⟨z,hz,hze⟩; exact hne z hz hze) (n := 2) (by norm_num)
  have hsD := differentiableOn_continuous_square_root isOpen_ball hg hsc (fun z _ => hs z) hne
  have hs0 : s 0^2=1 := (hs 0).trans h0
  refine ⟨fun z => s z*s 0,hsD.mul_const _,by simpa only [pow_two] using hs0,?_⟩
  intro z hz
  rw [mul_pow,hs z,hs0,mul_one]

/-- Every normalized disk-univalent map has a normalized odd univalent
square-root transform on the same disk. -/
theorem univalent_odd_square_root {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (hf0 : f 0=0) (hd0 : deriv f 0=1) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (ball 0 1) ∧ InjOn h (ball 0 1) ∧
      h 0=0 ∧ deriv h 0=1 ∧
      (∀ z∈ball (0:ℂ) 1, h z^2=f (z^2)) ∧ (∀ z, h (-z)= -h z) := by
  have hzero : (0:ℂ)∈ball 0 1 := mem_ball_self zero_lt_one
  let g := dslope f 0
  have hg : DifferentiableOn ℂ g (ball 0 1) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds (0:ℂ) zero_lt_one)).mpr hf
  have hg0 : g 0=1 := by simpa [g] using hd0
  have hgne (z : ℂ) (hz : z∈ball (0:ℂ) 1) : g z≠0 := by
    by_cases hz0 : z=0
    · simpa only [hz0,hg0] using one_ne_zero
    · dsimp only [g]
      rw [dslope_of_ne _ hz0,slope_def_field,hf0,sub_zero,sub_zero]
      exact div_ne_zero (fun h => hz0 (hi hz hzero (h.trans hf0.symm))) hz0
  obtain ⟨q,hq,hq0,hq2⟩ := exists_normalized_analytic_square_root hg hgne hg0
  let h (z : ℂ) := z*q (z^2)
  have hsq (z : ℂ) (hz : z∈ball (0:ℂ) 1) : z^2∈ball (0:ℂ) 1 := by
    rw [mem_ball,dist_zero_right,norm_pow]
    exact pow_lt_one₀ (norm_nonneg z) (by simpa using hz) (by norm_num)
  have hh : DifferentiableOn ℂ h (ball 0 1) :=
    differentiableOn_id.mul (hq.comp (differentiable_id.pow 2).differentiableOn hsq)
  have hh0 : h 0=0 := by simp [h]
  have hhD : deriv h 0=1 := by
    have hdq := ((hq.differentiableAt (isOpen_ball.mem_nhds (hsq 0 hzero))).hasDerivAt).comp 0
      (hasDerivAt_pow 2 (0:ℂ))
    have hd := (hasDerivAt_id (0:ℂ)).mul hdq
    change HasDerivAt h _ 0 at hd
    simpa [hq0] using hd.deriv
  have hh2 (z : ℂ) (hz : z∈ball (0:ℂ) 1) : h z^2=f (z^2) := by
    dsimp only [h]
    rw [mul_pow,hq2 _ (hsq z hz)]
    have he := sub_smul_dslope f 0 (z^2)
    simpa only [sub_zero,hf0,smul_eq_mul] using he
  have hodd (z : ℂ) : h (-z)= -h z := by simp [h]
  refine ⟨h,hh,?_,hh0,hhD,hh2,hodd⟩
  intro z hz w hw he
  have he2 : z^2=w^2 := hi (hsq z hz) (hsq w hw)
    ((hh2 z hz).symm.trans ((congrArg (fun v : ℂ => v^2) he).trans (hh2 w hw)))
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he2 with hzw | hzw
  · exact hzw
  · have hhz : h z=0 := by
      have he' : h z= -h z := he.trans (by rw [show w= -z by rw [hzw,neg_neg],hodd])
      linear_combination (1/2:ℂ)*he'
    have hz2 : z^2=0 := hi (hsq z hz) hzero (by rw [←hh2 z hz,hhz,hf0]; simp)
    have hz0 : z=0 := (pow_eq_zero_iff (by norm_num : (2:ℕ)≠0)).mp hz2
    rw [hz0] at hzw
    rw [hz0]
    simpa [eq_comm] using hzw

end SLEExactGauge

end

end OAI
