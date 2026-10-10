import OAI.Geometry.RCD.Sobolev.VarianceLowerBound

namespace OAI

/-! # Scalar integration of the Fisher curvature inequality -/

open Set
namespace RegularPointCoordinates

theorem fisher_exponential_lower {I : ℝ → ℝ} {K s : ℝ} (hs : 0 ≤ s)
    (hc : ContinuousOn I (Icc 0 s))
    (hd : ∀ t∈Ioo 0 s, ∃ d : ℝ, HasDerivAt I d t ∧ 2*K*I t≤d) :
    I 0≤Real.exp (-2*K*s)*I s := by
  let J := fun t => Real.exp (-2*K*t)*I t
  have hder (t : ℝ) (ht : t∈Ioo 0 s) : ∃ d : ℝ, HasDerivAt J d t ∧ 0≤d := by
    obtain ⟨d,hi,hbound⟩ := hd t ht
    have he := (((hasDerivAt_id t).const_mul (-2*K)).exp).mul hi
    simp only [id_eq,mul_one] at he
    refine ⟨_,he,?_⟩
    have hp := mul_nonneg (Real.exp_pos (-2*K*t)).le (sub_nonneg.mpr hbound)
    nlinarith only [hp]
  have hm : MonotoneOn J (Icc 0 s) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 s)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc)
    · rw [interior_Icc]
      intro t ht
      exact (hder t ht).choose_spec.1.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨d,hd,hn⟩ := hder t ht
      change 0≤deriv J t
      rwa [hd.deriv]
  simpa only [J,mul_zero,Real.exp_zero,one_mul] using
    hm ⟨le_rfl,hs⟩ ⟨hs,le_rfl⟩ hs

theorem fisher_entropy_lower {I F : ℝ → ℝ} {K T : ℝ} (hT : 0<T)
    (hI0 : 0≤I 0) (hIc : ContinuousOn I (Ico 0 T))
    (hId : ∀ t∈Ioo 0 T, ∃ d : ℝ, HasDerivAt I d t ∧ 2*K*I t≤d)
    (hFc : ContinuousOn F (Icc 0 T))
    (hFd : ∀ t∈Ioo 0 T, HasDerivAt F (I t) t) :
    T*Real.exp (-2*|K| * T)*I 0≤F T-F 0 := by
  have hh := variance_lower_bound (K:=K) (E:=I 0/2) hT (by positivity) hFc
    (fun t ht => ⟨I t/2,by convert hFd t ht using 1; ring,?_⟩)
  · nlinarith only [hh]
  · have hi := fisher_exponential_lower ht.1.le
      (hIc.mono (fun a ha => ⟨ha.1,ha.2.trans_lt ht.2⟩))
      (fun a ha => hId a ⟨ha.1,ha.2.trans ht.2⟩)
    linarith only [hi]

end RegularPointCoordinates

end OAI
