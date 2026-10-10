import OAI.Probability.InvariantIsing.Magnetic.MagneticHeightSupport
import OAI.Probability.InvariantIsing.Magnetic.MagneticBoundaryContinuity

namespace OAI

/-! The constrained supporting inequality on the full nonnegative height
cone, including repeated levels and zero variances. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem magneticHeight_support (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    constrainedFieldValue (fieldWithHeights h r hr0 hrmono) m ≤ constrainedFieldValue h m +
      ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticFieldLevel h m i) *
        (r i - h.height i) := by
  let k := fieldWithHeights h r hr0 hrmono
  have hleft := continuous_fieldRegularizedConstrainedValue k hm
  have hright : Continuous (fun t => constrainedFieldValue (fieldRegularized h t) m +
      ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i)) := by
    have hval := continuous_fieldRegularizedConstrainedValue h hm
    have hB := continuous_fieldRegularizedMagneticLevel h hm
    fun_prop
  have hineq : ∀ t ∈ Ioc (0 : ℝ) 1,
      constrainedFieldValue (fieldRegularized k t) m ≤
        constrainedFieldValue (fieldRegularized h t) m +
          ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
            magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i) := by
    intro t ht
    have hh : (fieldRegularized h t).height ∈ fieldStrictHeightCone h.depth :=
      fieldRegularized_strict h ht
    have hk : (fieldRegularized k t).height ∈ fieldStrictHeightCone h.depth :=
      fieldRegularized_strict k ht
    have heh : fieldStepOfStrictHeights h (fieldRegularized h t).height hh =
        fieldRegularized h t := by
      unfold fieldStepOfStrictHeights fieldRegularized fieldWithHeights
      rfl
    have hek : fieldStepOfStrictHeights h (fieldRegularized k t).height hk =
        fieldRegularized k t := by
      unfold fieldStepOfStrictHeights fieldRegularized fieldWithHeights k
      rfl
    have hi := magneticHeight_support_strict h hm _ _ hh hk
    have hevh := congrArg (fun q : FieldStep => constrainedFieldValue q m) heh
    have hevk := congrArg (fun q : FieldStep => constrainedFieldValue q m) hek
    rw [hevh, hevk] at hi
    have hd (i : Fin (h.depth + 1)) : (fieldRegularized k t).height i -
        (fieldRegularized h t).height i = r i - h.height i := by
      change (r i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) -
        (h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) = _
      ring
    have heBsum :
        (∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldStepOfStrictHeights h (fieldRegularized h t).height hh) m i) *
            ((fieldRegularized k t).height i - (fieldRegularized h t).height i)) =
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldRegularized h t) m i) *
            (r i - h.height i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [magneticFieldLevel_congr heh m i i rfl, hd]
    exact hi.trans_eq (congrArg
      (fun a : ℝ => constrainedFieldValue (fieldRegularized h t) m + a) heBsum)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      constrainedFieldValue (fieldRegularized k t) m ≤
        constrainedFieldValue (fieldRegularized h t) m +
          ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
            magneticFieldLevel (fieldRegularized h t) m i) * (r i - h.height i) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hineq t ⟨ht, ht1.le⟩
  have hh := le_of_tendsto_of_tendsto
    (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent
  have hz (i : Fin (h.depth + 1)) :=
    magneticFieldLevel_congr (fieldRegularized_zero h) m i i rfl
  simp_rw [hz] at hh
  simpa only [fieldRegularized_zero, k] using hh

end InvariantIsing

end

end OAI
