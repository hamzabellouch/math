import OAI.Probability.InvariantIsing.Fields.FieldHeightBoundaryContinuity

namespace OAI

/-! The actual finite scalar-field supporting inequality on the closed
nonnegative height cone. The proof removes the strict approximation by
continuity of both the value and its physical magnetization coefficients. -/

noncomputable section
open IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

theorem fieldHeight_support (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) :
    fieldValue (fieldWithHeights h r hr0 hrmono) 0 ≤ fieldValue h 0 +
      ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 * fieldMagnetizationLevel h i) *
        (r i - h.height i) := by
  let k := fieldWithHeights h r hr0 hrmono
  have hleft := continuous_fieldRegularizedValue k
  have hright : Continuous (fun t => fieldValue (fieldRegularized h t) 0 +
      ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
        fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i)) := by
    have hval := continuous_fieldRegularizedValue h
    have hB := continuous_fieldRegularizedMagnetization h
    fun_prop
  have hineq : ∀ t ∈ Ioc (0 : ℝ) 1,
      fieldValue (fieldRegularized k t) 0 ≤ fieldValue (fieldRegularized h t) 0 +
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i) := by
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
    have hi := fieldHeight_support_strict h _ _ hh hk
    have hevh := congrArg (fun q : FieldStep => fieldValue q 0) heh
    have hevk := congrArg (fun q : FieldStep => fieldValue q 0) hek
    rw [hevh, hevk] at hi
    have hd (i : Fin (h.depth + 1)) : (fieldRegularized k t).height i -
        (fieldRegularized h t).height i = r i - h.height i := by
      change (r i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) -
        (h.height i + fieldHeightEpsilon t * (i.val + 1 : ℕ)) = _
      ring
    have heBsum :
        (∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldStepOfStrictHeights h (fieldRegularized h t).height hh) i) *
            ((fieldRegularized k t).height i - (fieldRegularized h t).height i)) =
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) *
            (r i - h.height i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fieldMagnetizationLevel_congr heh i i rfl, hd]
    exact hi.trans_eq (congrArg (fun a : ℝ => fieldValue (fieldRegularized h t) 0 + a) heBsum)
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      fieldValue (fieldRegularized k t) 0 ≤ fieldValue (fieldRegularized h t) 0 +
        ∑ i : Fin (h.depth + 1), (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          fieldMagnetizationLevel (fieldRegularized h t) i) * (r i - h.height i) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hineq t ⟨ht, ht1.le⟩
  have hh := le_of_tendsto_of_tendsto
    (hleft.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hright.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hevent
  have hz (i : Fin (h.depth + 1)) :=
    fieldMagnetizationLevel_congr (fieldRegularized_zero h) i i rfl
  simp_rw [hz] at hh
  simpa only [fieldRegularized_zero, k] using hh

end InvariantIsing

end

end OAI
