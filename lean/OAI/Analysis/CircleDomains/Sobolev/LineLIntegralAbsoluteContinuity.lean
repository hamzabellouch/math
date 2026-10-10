import OAI.Analysis.CircleDomains.Sobolev.IntegralLineAbsoluteContinuity

namespace OAI

/-! The line-integral criterion in extended nonnegative form. It applies
directly to the measurable path densities used by the barrier. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CircleDomainRigidity

open AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X]

theorem absolutelyContinuousOnInterval_of_lintegral_bound
    {f : ℝ → X} {g : ℝ → ℝ≥0∞} {a b : ℝ}
    (hg : (∫⁻t in uIoc a b, g t) < ∞)
    (hfg : ∀x ∈ uIcc a b, ∀y ∈ uIcc a b,
      ENNReal.ofReal (dist (f x) (f y)) ≤ ∫⁻t in uIoc x y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  let S (E : ℕ × (ℕ → ℝ × ℝ)) := ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hlim : Tendsto (fun E => ∫⁻t in S E, g t ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero hg.ne (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero a b)
  have hr := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hlim
  simp only [ENNReal.toReal_zero] at hr
  apply squeeze_zero' (Eventually.of_forall fun E =>
    Finset.sum_nonneg (fun _ _ => dist_nonneg)) _ hr
  have hev : ∀ᶠ E in totalLengthFilter ⊓ 𝓟 (disjWithin a b), E ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hev] with E hE
  have hfin : (∫⁻t in S E, g t ∂volume.restrict (uIoc a b)) ≠ ∞ :=
    (lt_of_le_of_lt (lintegral_mono_set (subset_univ (S E)))
      (by simpa only [Measure.restrict_univ] using hg)).ne
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)]
  change (∑i ∈ Finset.range E.1, ENNReal.ofReal (dist (f (E.2 i).1) (f (E.2 i).2))) ≤
    ∫⁻t in ⋃i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2,
      g t ∂volume.restrict (uIoc a b)
  rw [lintegral_biUnion_finset hE.2 (fun _ _ => measurableSet_uIoc)]
  apply Finset.sum_le_sum
  intro i hi
  rw [Measure.restrict_restrict_of_subset
    (uIoc_subset_of_mem_disjWithin hE (Finset.mem_range.mp hi))]
  exact hfg _ (hE.1 i hi).1 _ (hE.1 i hi).2

end CircleDomainRigidity

end OAI
