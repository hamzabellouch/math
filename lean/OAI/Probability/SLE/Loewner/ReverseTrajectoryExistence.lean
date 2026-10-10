import OAI.Probability.SLE.Loewner.TargetInverseExistence

namespace OAI

/-! The unclipped reverse equation has a global trajectory from every
point of the upper half-plane, for every continuous real driver. -/
noncomputable section
open Set Filter Complex _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology

namespace SLEExactGauge

theorem exists_reverse_trajectory (u : ℝ → ℝ) (hu : Continuous u)
    (w : ℂ) (hw : 0 < w.im) :
    ∃ q : ℝ → ℂ, q 0=w ∧
      (∀ t, 0 ≤ t → w.im ≤ (q t).im) ∧
      ∀ t, 0 ≤ t → HasDerivWithinAt q (-2/(q t-(u t : ℂ))) (Ici 0) t := by
  let a : ℝ := w.im/2
  have ha : 0 < a := half_pos hw
  obtain ⟨Q,_,hQ0,hQd⟩ := exists_measurable_reverse_flow
    (fun t (_ : Unit) => u t) (hu.measurable.comp measurable_fst)
    (fun _ => hu) (fun _ => w) measurable_const ha
  let q : ℝ → ℂ := fun t => Q t ()
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt q
      (reverseField a (u t) (q t)) (Ici 0) t := hQd () t ht
  have hqc : ContinuousOn q (Ici 0) := fun t ht => (hd t ht).continuousWithinAt
  have hm : MonotoneOn (fun t => (q t).im) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (Complex.continuous_im.comp_continuousOn hqc)
      (fun t ht => (Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t
        (hd t (interior_subset ht))).mono interior_subset)
    intro t ht
    exact reverseField_im_nonneg ha _ _
  have hq0 : q 0=w := hQ0 ()
  have hheight (t : ℝ) (ht : 0 ≤ t) : w.im ≤ (q t).im := by
    rw [← hq0]
    exact hm (show 0 ∈ Ici (0 : ℝ) from le_refl (0 : ℝ)) ht ht
  refine ⟨q,hq0,hheight,?_⟩
  intro t ht
  have h := hd t ht
  rw [reverseField,reverseCenter_eq ((half_le_self hw.le).trans (hheight t ht))] at h
  simpa only [div_eq_mul_inv] using h

end SLEExactGauge

end

end OAI
