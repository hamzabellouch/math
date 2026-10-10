import OAI.Analysis.TriangularHilbert.HardPairing

namespace OAI

section
namespace TriangularHilbert.Heat
open MeasureTheory Filter
open scoped Topology
noncomputable section

lemma abs_hardKernel_le {r R : ℝ} (hr : 0 < r) (hb : r ≤ R) (t : ℝ) : |hardKernel r R t| ≤ 1/r := by
  unfold hardKernel
  by_cases hrt : r < |t|
  · by_cases hRt : R < |t|
    · simp [hrt,hRt,hr.le]
    · simp only [hrt,hRt,ite_true,ite_false,sub_zero,abs_div,abs_one]
      exact one_div_le_one_div_of_le hr hrt.le
  · have hRt : ¬R < |t| := fun h => hrt (hb.trans_lt h)
    simp [hrt,hRt,hr.le]

lemma measurable_hardKernel (r R : ℝ) : Measurable (hardKernel r R) := by
  unfold hardKernel
  exact ((measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const).sub
    (measurable_const.ite (measurableSet_lt measurable_const measurable_abs) measurable_const)).div measurable_id

lemma continuousAt_absStep (r t : ℝ) (ht : |t| ≠ r) :
    ContinuousAt (fun x : ℝ => if r < |x| then (1:ℝ) else 0) t := by
  rcases lt_or_gt_of_ne ht with h|h
  · have he : ∀ᶠ x in 𝓝 t, |x| < r := continuous_abs.continuousAt.eventually (eventually_lt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (0:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [not_lt.mpr hx.le,ite_false]
  · have he : ∀ᶠ x in 𝓝 t, r < |x| := continuous_abs.continuousAt.eventually (eventually_gt_nhds h)
    apply (show ContinuousAt (fun _ : ℝ => (1:ℝ)) t from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [he] with x hx
    simp only [hx,ite_true]

lemma continuousAt_hardKernel (r R t : ℝ) (ht0 : t ≠ 0) (htr : |t| ≠ r) (htR : |t| ≠ R) :
    ContinuousAt (hardKernel r R) t :=
  ((continuousAt_absStep r t htr).sub (continuousAt_absStep R t htR)).div continuousAt_id ht0
end
end TriangularHilbert.Heat
end

end OAI
