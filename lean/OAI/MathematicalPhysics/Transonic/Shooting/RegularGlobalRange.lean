import OAI.MathematicalPhysics.Transonic.Shooting.RegularGlobalControl

namespace OAI

section

namespace SepticProfile.IntegerPolynomial
open Set RegularContinuation

lemma stepTime_zero (R : ℤ) (a : Step) : stepTime R a.Z a.H 0=startTime R a := by
  simp [stepTime,coordinate,startTime]
lemma stepTime_one (R : ℤ) (a : Step) : stepTime R a.Z a.H 1=stopTime R a := by
  simp [stepTime,coordinate,stopTime]
lemma start_eq_stop {R : ℤ} {a b : Step} (h : a.Z-a.H=b.Z) :
    startTime R b=stopTime R a := by rw [stopTime,startTime,h]

/-- The same integer certificate also certifies that the clamp is inactive
at every point, not only the mesh endpoints. -/
theorem global_step_range {S SN K KN R Q : ℤ} (hs : 0<S) (hk : 0<K) (hr : 0<R)
    (hq : 0<Q) (hsigma : ((SN:ℝ)/S) ∈ Icc (0:ℝ) 1) {a : Step}
    (ha : Valid S SN K KN R Q a) {u : ℝ → ℝ}
    (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u (globalField (SN/S) (KN/K) t (u t))
      (Icc 0 (9/100)) t)
    (hu0 : u (startTime R a) ∈ Icc ((head a.lo:ℝ)/Q) ((head a.hi:ℝ)/Q)) :
    ∀ t ∈ Icc (startTime R a) (stopTime R a), u t ∈ Icc (0:ℝ) (999/1000) := by
  have hd := localized_derivative hr ha.1 ha.2.2.1 ha.2.1 hud
  have hc : ContinuousOn (u ∘ stepTime R a.Z a.H) (Icc 0 1) :=
    fun s hs => (hd s hs).continuousWithinAt
  have hzero : (u ∘ stepTime R a.Z a.H) 0=u (startTime R a) := by rw [Function.comp_apply,stepTime_zero]
  have hb := step_control hs hk hr hq hsigma ha hc hd (hzero.symm ▸ hu0)
  intro t ht
  have hm : t ∈ Icc (stepTime R a.Z a.H 0) (stepTime R a.Z a.H 1) := by
    simpa only [stepTime_zero,stepTime_one] using ht
  obtain ⟨s,hs',hst⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1)
    (fun x hx => (hasDerivAt_stepTime R a.Z a.H x).continuousAt.continuousWithinAt) hm
  have hl := range_velocity hq ha.2.2.2.1 hs'
  have hu := range_velocity hq ha.2.2.2.2.1 hs'
  have hh := hb s hs'
  simp only [Function.comp_apply,hst] at hh
  exact ⟨hl.1.trans hh.1,hh.2.trans hu.2⟩

lemma unclamped_derivative {sigma kappa : ℝ} {u : ℝ → ℝ}
    (hud : ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u (globalField sigma kappa t (u t))
      (Icc 0 (9/100)) t)
    (hrange : ∀ t ∈ Icc (0:ℝ) (9/100), u t ∈ Icc (0:ℝ) (999/1000)) :
    ∀ t ∈ Icc (0:ℝ) (9/100), HasDerivWithinAt u
      (-numer kappa (99/100-t) (u t)/denom sigma (99/100-t) (u t)) (Icc 0 (9/100)) t := by
  intro t ht
  simpa only [globalField,clamp_eq (hrange t ht)] using hud t ht
end SepticProfile.IntegerPolynomial


end

end OAI
