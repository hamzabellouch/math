import OAI.Analysis.CircleDomains.Sobolev.WeakPairDifferential

namespace OAI

/-! Two scalar weak-gradient errors control the actual joint linear
map, without any extra integrability assumption on that map. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPairDifferential_norm_le (a b : EuclideanPlane) :
    ‖weakPairDifferential a b‖ ≤ ‖a‖+‖b‖ := by
  have hn := norm_add_le ((innerSL ℝ a).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    ((innerSL ℝ b).smulRight (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  simpa only [weakPairDifferential, ContinuousLinearMap.norm_smulRight_apply,
    innerSL_apply_norm, PiLp.norm_single, norm_one, mul_one] using hn

 theorem weakPairDifferential_sub (a b c d : EuclideanPlane) :
    weakPairDifferential (a-c) (b-d) = weakPairDifferential a b-weakPairDifferential c d := by
  ext x
  simp only [weakPairDifferential, add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    map_sub, sub_smul]
  abel_nf

 theorem continuous_weakPairDifferential : Continuous (fun x : EuclideanPlane × EuclideanPlane =>
    weakPairDifferential x.1 x.2) := by
  have hc (e : EuclideanPlane) : Continuous (fun a : EuclideanPlane => (innerSL ℝ a).smulRight e) :=
    ((ContinuousLinearMap.smulRightL ℝ EuclideanPlane EuclideanPlane).continuous.comp
      (innerSL ℝ).continuous).clm_apply continuous_const
  exact ((hc _).comp continuous_fst).add ((hc _).comp continuous_snd)

 theorem weakPairDifferential_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b : X → EuclideanPlane} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    MemLp (fun x => weakPairDifferential (a x) (b x)) 2 μ ∧
      (eLpNorm (fun x => weakPairDifferential (a x) (b x)) 2 μ).toReal ≤
        (eLpNorm a 2 μ).toReal+(eLpNorm b 2 μ).toReal := by
  have hm := continuous_weakPairDifferential.comp_aestronglyMeasurable
    (ha.aestronglyMeasurable.prodMk hb.aestronglyMeasurable)
  have hz : MemLp (fun _ : X => (0 : ℝ)) 2 μ := MemLp.zero'
  have h := l2_three_term_bound (a := 1) (b := 1) (c := 0) (by norm_num) (by norm_num)
    le_rfl hm ha.norm hb.norm hz
    (Eventually.of_forall (fun _ => norm_nonneg _))
    (Eventually.of_forall (fun _ => norm_nonneg _)) (Eventually.of_forall (fun _ => le_rfl))
    (Eventually.of_forall (fun x => by simpa only [one_mul, zero_mul, add_zero] using (weakPairDifferential_norm_le (a x) (b x))))
  simpa only [eLpNorm_norm _ ha.aestronglyMeasurable, eLpNorm_norm _ hb.aestronglyMeasurable,
    one_mul, zero_mul, add_zero] using h

 theorem weakPairDifferential_error_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {a b c d : X → EuclideanPlane}
    (ha : MemLp (fun x => a x-c x) 2 μ) (hb : MemLp (fun x => b x-d x) 2 μ) :
    MemLp (fun x => weakPairDifferential (a x) (b x)-weakPairDifferential (c x) (d x)) 2 μ ∧
      (eLpNorm (fun x => weakPairDifferential (a x) (b x)-weakPairDifferential (c x) (d x)) 2 μ).toReal ≤
        (eLpNorm (fun x => a x-c x) 2 μ).toReal+(eLpNorm (fun x => b x-d x) 2 μ).toReal := by
  simpa only [weakPairDifferential_sub] using weakPairDifferential_memLp ha hb

end CircleDomainRigidity

end

end OAI
