import OAI.Probability.InvariantIsing.Magnetic.MagneticHeightLipschitz
import OAI.Probability.InvariantIsing.Magnetic.MagneticBoundaryContinuity

namespace OAI

/-! The uniform height modulus extends to zero and repeated covariance
levels by the actual strict regularization and its bias continuity. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem constrainedFieldValue_height_lipschitz (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    |constrainedFieldValue (fieldWithHeights h r hr0 hrmono) s - constrainedFieldValue h s| ≤
      (1 / 2 : ℝ) * ∑ i, (h.cut i.succ - h.cut i.castSucc) * |r i - h.height i| := by
  let k := fieldWithHeights h r hr0 hrmono
  have hc : Continuous (fun t =>
      |constrainedFieldValue (fieldRegularized k t) s -
        constrainedFieldValue (fieldRegularized h t) s|) :=
    ((continuous_fieldRegularizedConstrainedValue k hs).sub
      (continuous_fieldRegularizedConstrainedValue h hs)).abs
  have hineq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
      |constrainedFieldValue (fieldRegularized k t) s -
        constrainedFieldValue (fieldRegularized h t) s| ≤
        (1 / 2 : ℝ) * ∑ i, (h.cut i.succ - h.cut i.castSucc) * |r i - h.height i| := by
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
    have hi := constrainedFieldValue_strict_lipschitz h hs _ _ hh hk
    rw [congrArg (fun v : FieldStep => constrainedFieldValue v s) heh,
      congrArg (fun v : FieldStep => constrainedFieldValue v s) hek] at hi
    have he (i : Fin (h.depth + 1)) : (fieldRegularized k t).height i -
        (fieldRegularized h t).height i = r i - h.height i := by
      change (r i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) -
        (h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) = _
      ring
    simpa only [he] using hi
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |constrainedFieldValue (fieldRegularized k t) s -
        constrainedFieldValue (fieldRegularized h t) s| ≤
        (1 / 2 : ℝ) * ∑ i, (h.cut i.succ - h.cut i.castSucc) * |r i - h.height i| := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hineq t ⟨ht, ht1.le⟩
  have hh := le_of_tendsto_of_tendsto
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds hevent
  simpa only [fieldRegularized_zero, k] using hh

end InvariantIsing

end

end OAI
