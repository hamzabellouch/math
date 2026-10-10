import OAI.Probability.SLE.Geometry.FiniteSimpleSlit
import OAI.Probability.SLE.Geometry.PublishedFiniteBoundaryExtension

namespace OAI

/-! Geometric concatenation of an old simple slit and a fresh simple slit
through its inverse chart. The resulting curve has no extra filled components. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

def concatenateSlit (T : ℝ≥0) (β η : ℝ≥0 → ℂ) (F : ℂ → ℂ) (u : ℝ)
    (t : ℝ≥0) : ℂ := if t ≤ T then β t else F ((u:ℂ)+η (t-T))

lemma continuous_concatenateSlit
    (T : ℝ≥0) (β η : ℝ≥0 → ℂ) (F : ℂ → ℂ) (u : ℝ)
    (hβ : Continuous β) (hη : Continuous η) (hη0 : η 0=0)
    (hηH : ∀ t, 0 ≤ (η t).im) (hF : ContinuousOn F closedHalfPlane)
    (hF0 : F (u:ℂ)=β T) : Continuous (concatenateSlit T β η F u) := by
  have hc : Continuous (fun t : ℝ≥0 => F ((u:ℂ)+η (t-T))) := by
    apply hF.comp_continuous (continuous_const.add (hη.comp (continuous_id.sub continuous_const)))
    intro t
    change 0 ≤ ((u:ℂ)+η (t-T)).im
    simpa only [closedHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using hηH (t-T)
  change Continuous ((Iic T).piecewise β (fun t => F ((u:ℂ)+η (t-T))))
  apply Continuous.piecewise _ hβ hc
  intro t ht
  have he : t=T := by simpa only [frontier_Iic,mem_singleton_iff] using ht
  simp only [he,tsub_self,hη0,add_zero,hF0]

lemma concatenateSlit_injective
    (T : ℝ≥0) (β η : ℝ≥0 → ℂ) (F : ℂ → ℂ) (u : ℝ)
    (hβ : InjOn β (Icc 0 T)) (hη : Function.Injective η)
    (hηH : ∀ t, 0 < t → η t ∈ upperHalfPlane)
    (hF : InjOn F upperHalfPlane)
    (himage : MapsTo F upperHalfPlane (survivingDomain β T)) :
    Function.Injective (concatenateSlit T β η F u) := by
  have hnew (t : ℝ≥0) (ht : T < t) : (u:ℂ)+η (t-T) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using
      hηH (t-T) (tsub_pos_iff_lt.mpr ht)
  intro s t he
  by_cases hs : s ≤ T
  · by_cases ht : t ≤ T
    · exact hβ ⟨zero_le,hs⟩ ⟨zero_le,ht⟩ (by simpa only [concatenateSlit,ite_eq_left hs,ite_eq_left ht] using he)
    · have him := himage (hnew t (lt_of_not_ge ht))
      apply False.elim
      apply him.1.2
      refine ⟨s,⟨zero_le,hs⟩,?_⟩
      simpa only [concatenateSlit,ite_eq_left hs,ite_eq_right ht] using he
  · by_cases ht : t ≤ T
    · have him := himage (hnew s (lt_of_not_ge hs))
      apply False.elim
      apply him.1.2
      refine ⟨t,⟨zero_le,ht⟩,?_⟩
      simpa only [concatenateSlit,ite_eq_right hs,ite_eq_left ht] using he.symm
    · have hst := hF (hnew s (lt_of_not_ge hs)) (hnew t (lt_of_not_ge ht))
        (by simpa only [concatenateSlit,ite_eq_right hs,ite_eq_right ht] using he)
      have heη := hη (add_left_cancel hst)
      exact (tsub_left_inj (le_of_not_ge hs) (le_of_not_ge ht)).mp heη

lemma concatenateSlit_positive
    (T : ℝ≥0) (β η : ℝ≥0 → ℂ) (F : ℂ → ℂ) (u : ℝ)
    (hβ : ∀ t, 0 < t → β t ∈ upperHalfPlane)
    (hη : ∀ t, 0 < t → η t ∈ upperHalfPlane)
    (hF : MapsTo F upperHalfPlane upperHalfPlane)
    (t : ℝ≥0) (ht : 0 < t) : concatenateSlit T β η F u t ∈ upperHalfPlane := by
  by_cases h : t ≤ T
  · simpa only [concatenateSlit,ite_eq_left h] using hβ t ht
  · rw [concatenateSlit,ite_eq_right h]
    apply hF
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,zero_add] using
      hη (t-T) (tsub_pos_iff_lt.mpr (lt_of_not_ge h))

theorem concatenateSlit_free_complement
    (T : ℝ≥0) (β η : ℝ≥0 → ℂ) (F : ℂ → ℂ) (u : ℝ)
    (hβc : Continuous β) (hηc : Continuous η) (hβ0 : β 0=0) (hη0 : η 0=0)
    (hβi : InjOn β (Icc 0 T)) (hηi : Function.Injective η)
    (hβH : ∀ t, 0 < t → β t ∈ upperHalfPlane)
    (hηH : ∀ t, 0 < t → η t ∈ upperHalfPlane)
    (hFc : ContinuousOn F closedHalfPlane) (hF0 : F (u:ℂ)=β T)
    (hFi : InjOn F upperHalfPlane)
    (hFmap : MapsTo F upperHalfPlane (survivingDomain β T))
    (S : ℝ≥0) (hS : 0 < S) :
    upperHalfPlane \ ((concatenateSlit T β η F u) '' Icc 0 S) ⊆
      survivingDomain (concatenateSlit T β η F u) S := by
  have hηclosed (t : ℝ≥0) : 0 ≤ (η t).im := by
    by_cases ht : t=0
    · simp [ht,hη0]
    · exact (hηH t (pos_iff_ne_zero.mpr ht)).le
  apply finite_simple_slit_free _
    (continuous_concatenateSlit T β η F u hβc hηc hη0 hηclosed hFc hF0)
    (by simp only [concatenateSlit,ite_eq_left (show (0:ℝ≥0) ≤ T from zero_le),hβ0]) S hS
    (concatenateSlit_injective T β η F u hβi hηi hηH hFi hFmap).injOn
  intro t ht
  exact concatenateSlit_positive T β η F u hβH hηH
    (fun z hz => (hFmap hz).1.1) t ht.1

end SLEExactGauge

end

end OAI
