import OAI.Probability.SLE.Loewner.SlitUniformForwardBound
import OAI.Probability.SLE.Loewner.ReflectedExteriorHeight
import OAI.Probability.SLE.Loewner.InitialForwardJointContinuity

namespace OAI

/-! The normalized initial forward maps continued across the real axis
away from the attached slit. These are the same maps on the upper side. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology ComplexConjugate

namespace SLEExactGauge

noncomputable def initialReflectedChart (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) (hs : s≠0) : ReflectedCapacityChart (initialSubarc p s) :=
  Classical.choice (exists_reflectedCapacityChart (initialSubarc p s)
    (initialSubarc_injective hi hs) (by simpa only [initialSubarc_zero] using h0)
    (initialSubarc_upper hH hs))

noncomputable def initialReflectedForward (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) : ℂ → ℂ :=
  if hs : s=0 then id else (initialReflectedChart p hi h0 hH s hs).chart.forward

lemma reflected_initial_subset (p : C(unitInterval,ℂ)) (s : unitInterval) :
    reflectedArcSet (initialSubarc p s) ⊆ reflectedArcSet p := by
  intro z hz
  rcases hz with hz | ⟨w,hw,rfl⟩
  · exact Or.inl (initialSubarc_range_subset p s hz)
  · exact Or.inr ⟨w,initialSubarc_range_subset p s hw,rfl⟩

lemma initialReflectedForward_eq (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {z : ℂ} (hz : z∈upperHalfPlane \ range (initialSubarc p s)) :
    initialReflectedForward p hi h0 hH s z=initialForwardChart p hi h0 hH s z := by
  by_cases hs : s=0
  · subst s
    simp [initialReflectedForward]
  · simp only [initialReflectedForward,initialForwardChart,dite_eq_right hs]
    exact ((initialSlitChart p hi h0 hH s hs).unique_on_domain
      (initialReflectedChart p hi h0 hH s hs).chart).1 hz |>.symm

lemma initialReflectedForward_differentiable (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) :
    DifferentiableOn ℂ (initialReflectedForward p hi h0 hH s) (reflectedArcSet p)ᶜ := by
  by_cases hs : s=0
  · simp only [initialReflectedForward,dite_eq_left hs]
    exact differentiableOn_id
  · rw [initialReflectedForward,dite_eq_right hs]
    exact ((initialReflectedChart p hi h0 hH s hs).forward_differentiable
      (by simpa only [initialSubarc_zero] using h0)).mono
      (compl_subset_compl.mpr (reflected_initial_subset p s))

lemma real_not_reflected_arc (p : C(unitInterval,ℂ)) (h0 : p 0=0)
    (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {x : ℝ} (hx : x≠0) : (x:ℂ)∉reflectedArcSet p := by
  have hreal : (x:ℂ)∉range p := by
    rintro ⟨s,hs⟩
    by_cases hs0 : s=0
    · have he : (x:ℂ)=0 := by simpa only [hs0,h0] using hs.symm
      exact hx (ofReal_eq_zero.mp he)
    · have hh := hH s hs0
      rw [hs] at hh
      simp [upperHalfPlane] at hh
  rintro (hz | ⟨w,hw,he⟩)
  · exact hreal hz
  · apply hreal
    have hwx : w=(x:ℂ) := by
      have hh := congrArg conj he
      simpa only [conj_conj,conj_ofReal] using hh
    rwa [hwx] at hw

lemma initialReflectedForward_real (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    (s : unitInterval) {x : ℝ} (hx : x≠0) :
    (initialReflectedForward p hi h0 hH s (x:ℂ)).im=0 := by
  by_cases hs : s=0
  · simp [initialReflectedForward,hs]
  · rw [initialReflectedForward,dite_eq_right hs]
    have hh := (initialReflectedChart p hi h0 hH s hs).forward_reflection
      (fun hz => real_not_reflected_arc p h0 hH hx (reflected_initial_subset p s hz))
    rw [conj_ofReal] at hh
    have he := congrArg Complex.im hh
    simp only [conj_im] at he
    linarith

lemma initialReflectedForward_uniform_bound (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ s, ‖p s‖<R) (s : unitInterval)
    {z : ℂ} (hz : z∉reflectedArcSet p) (hzR : ‖z‖≤2*R) :
    ‖initialReflectedForward p hi h0 hH s z‖≤(512*Real.pi+9)*R := by
  by_cases hs : s=0
  · simp only [initialReflectedForward,dite_eq_left hs,id_eq]
    exact hzR.trans (by nlinarith [Real.pi_pos])
  · rw [initialReflectedForward,dite_eq_right hs]
    exact (initialReflectedChart p hi h0 hH s hs).forward_bounded_in_two_radius
      (initialSubarc_injective hi hs) (by simpa only [initialSubarc_zero] using h0)
      (initialSubarc_upper hH hs) hR (fun t => hp (s*t))
      (fun he => hz (reflected_initial_subset p s he)) hzR

end SLEExactGauge

end

end OAI
