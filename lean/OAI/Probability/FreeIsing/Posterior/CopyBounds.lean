import OAI.Probability.FreeIsing.Estimates.ProgressivePrimitiveFubini
import OAI.Probability.FreeIsing.Estimates.SharedInnovationBounds
import OAI.Probability.FreeIsing.Posterior.FieldMoments
import OAI.Probability.FreeIsing.Posterior.ProgressiveIsingPosterior

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem ae_observation_sub_bound_of_shared_progressive_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ t, ∀ᵐ ω ∂P, |m t ω| ≤ 1)
    (hb' : ∀ t, ∀ᵐ ω ∂P, |m' t ω| ≤ 1)
    {x x' w : Ω → ℝ} (t : ℝ≥0)
    (hx : ∀ᵐ ω ∂P, x ω = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, x' ω = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |x ω - x' ω| ≤ 2 * (t : ℝ) := by
  have hL := ae_lipschitzWith_nnrealTimePrimitive hm (C := 1) hb
  have hL' := ae_lipschitzWith_nnrealTimePrimitive hm' (C := 1) hb'
  filter_upwards [hL, hL', hx, hx'] with ω hω hω' hxω hxω'
  have h1 : |nnrealTimePrimitive m t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω.dist_le_mul t 0
  have h2 : |nnrealTimePrimitive m' t ω| ≤ (t : ℝ) := by
    simpa only [Real.dist_eq, nnrealTimePrimitive, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, NNReal.coe_one, one_mul,
      NNReal.dist_eq, abs_of_nonneg t.coe_nonneg] using hω'.dist_le_mul t 0
  rw [hxω, hxω']
  have heq : (w ω + nnrealTimePrimitive m t ω) -
      (w ω + nnrealTimePrimitive m' t ω) =
      nnrealTimePrimitive m t ω - nnrealTimePrimitive m' t ω := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith)

theorem HasFreeIsingLaw.gaussianPosteriorField_copy_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d)
    {q q' : Ω → (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)}
    (hq : MeasurePreserving q P (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hq' : MeasurePreserving q' P (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {F G : Filtration ℝ≥0 mΩ} {m m' : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (hm' : IsStronglyProgressive G m')
    (hb : ∀ s, ∀ᵐ ω ∂P, |m s ω| ≤ 1)
    (hb' : ∀ s, ∀ᵐ ω ∂P, |m' s ω| ≤ 1)
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, observation t (q ω) v = w ω + nnrealTimePrimitive m t ω)
    (hx' : ∀ᵐ ω ∂P, observation t (q' ω) v = w ω + nnrealTimePrimitive m' t ω) :
    ∀ᵐ ω ∂P, |gaussianPosteriorField μ t v (q ω) -
      gaussianPosteriorField μ t v (q' ω)| ≤ 2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation
    hm hm' hb hb' t hx hx'
  have hfield := hμ.gaussian_posterior_field_bound hbeta t v
  have hleft := hq.quasiMeasurePreserving.ae hfield
  have hright := hq'.quasiMeasurePreserving.ae hfield
  filter_upwards [hobs, hleft, hright] with ω hobsω hl hr
  have hlb := hl.2
  have hrb := hr.2
  change |gaussianPosteriorField μ t v (q ω) - observation t (q ω) v| ≤
    (d : ℝ) * beta at hlb
  change |gaussianPosteriorField μ t v (q' ω) - observation t (q' ω) v| ≤
    (d : ℝ) * beta at hrb
  have htriangle := abs_sub_le (gaussianPosteriorField μ t v (q ω))
    (observation t (q ω) v) (gaussianPosteriorField μ t v (q' ω))
  have htriangle' := abs_sub_le (observation t (q ω) v)
    (observation t (q' ω) v) (gaussianPosteriorField μ t v (q' ω))
  rw [abs_sub_comm (observation t (q' ω) v)] at htriangle'
  linarith

theorem HasFreeIsingLaw.gibbsField_bound_of_observation_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) {X : Ω → TreeVertex d → ℝ}
    (hX : IdentDistrib X (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) :
    ∀ᵐ ω ∂P, |Real.artanh (infiniteGibbsSpinMean beta v (X ω)) - X ω v| ≤
      (d : ℝ) * beta := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hmeas := (ha.comp (measurable_infiniteGibbsSpinMean beta v)).sub
    (measurable_pi_apply v)
  apply hX.symm.ae_snd (measurableSet_le hmeas.abs measurable_const)
  filter_upwards [hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.gaussian_posterior_field_bound hbeta t v] with p heq hp
  simp only [Pi.sub_apply, Function.comp_apply]
  rw [heq]
  exact hp.2

theorem HasFreeIsingLaw.gibbsField_copy_bound_of_shared_innovation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    ∀ᵐ ω ∂P,
      |Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))| ≤
          2 * (t : ℝ) + 2 * (d : ℝ) * beta := by
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hobs := ae_observation_sub_bound_of_shared_progressive_innovation hm hm'
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _))
    (fun s => Filter.Eventually.of_forall
      (fun p => infiniteGibbsSpinMean_abs_le_one beta v _)) t hx hx'
  have hl := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw
  have hr := hμ.gibbsField_bound_of_observation_identDistrib hbeta t v hlaw'
  filter_upwards [hobs, hl, hr] with ω hobsω hlω hrω
  have htriangle := abs_sub_le
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)))
    (X v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  have htriangle' := abs_sub_le (X v t ω) (X' v t ω)
    (Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω)))
  rw [abs_sub_comm (X' v t ω)] at htriangle'
  linarith

theorem HasFreeIsingLaw.gibbsField_copy_secondMoment_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F G : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive G (X' i))
    (t : ℝ≥0) (v : TreeVertex d)
    (hlaw : IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {w : Ω → ℝ}
    (hx : ∀ᵐ ω ∂P, X v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ᵐ ω ∂P, X' v t ω = w ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    MemLp U 2 P ∧ 0 ≤ (∫ ω, (U ω) ^ 2 ∂P) ∧
      (∫ ω, (U ω) ^ 2 ∂P) ≤ (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
  dsimp only
  have hb := hμ.gibbsField_copy_bound_of_shared_innovation hbeta hX hX'
    t v hlaw hlaw' hx hx'
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean G beta v X' hX'
  have hmeas := (ha.comp (((hm.stronglyAdapted t).mono (F.le t)).measurable)).sub
    (ha.comp (((hm'.stronglyAdapted t).mono (G.le t)).measurable))
  exact discrepancy_secondMoment_bounds hmeas.aestronglyMeasurable hb

theorem progressive_memLp_two_on_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {U : ℝ≥0 → Ω → ℝ}
    (hU : IsStronglyProgressive F U) (T : ℝ≥0) (C : ℝ)
    (hb : ∀ t ≤ T, ∀ᵐ ω ∂P, |U t ω| ≤ C) :
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P,
      |U p.1.toNNReal p.2| ≤ C) ∧
    MemLp (fun p : ℝ × Ω => U p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (T : ℝ))
  have hclip : StronglyMeasurable (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) :=
    (stronglyMeasurable_clipped_nnreal_process hU T).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (F.le T)))
  have hbc : ∀ᵐ p ∂ν.prod P, |U (min p.1.toNNReal T) p.2| ≤ C := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hclip.measurable.abs measurable_const)).2
    exact Filter.Eventually.of_forall fun r => hb _ (min_le_right r.toNNReal T)
  have hc : MemLp (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) 2 (ν.prod P) :=
    MemLp.of_bound hclip.aestronglyMeasurable C
      (by simpa only [Real.norm_eq_abs] using hbc)
  have heq : (fun p : ℝ × Ω => U (min p.1.toNNReal T) p.2) =ᵐ[ν.prod P]
      (fun p => U p.1.toNNReal p.2) := by
    have hmem : ∀ᵐ p ∂ν.prod P, p.1 ∈ Ioc (0 : ℝ) (T : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    have ht : p.1.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hp.2
    simp only [min_eq_left ht]
  refine ⟨?_, MemLp.ae_eq heq hc⟩
  filter_upwards [heq, hbc] with p heq hp
  rwa [← heq]

theorem HasFreeIsingLaw.gibbsField_copy_joint_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {F : Filtration ℝ≥0 mΩ}
    {X X' : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hX : ∀ i, IsStronglyProgressive F (X i))
    (hX' : ∀ i, IsStronglyProgressive F (X' i))
    (T : ℝ≥0) (v : TreeVertex d)
    (hlaw : ∀ t ≤ T, IdentDistrib (fun ω i => X i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    (hlaw' : ∀ t ≤ T, IdentDistrib (fun ω i => X' i t ω) (observation t) P
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)))
    {W : ℝ≥0 → Ω → ℝ}
    (hx : ∀ t ≤ T, ∀ᵐ ω ∂P, X v t ω = W t ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X i s p)) t ω)
    (hx' : ∀ t ≤ T, ∀ᵐ ω ∂P, X' v t ω = W t ω + nnrealTimePrimitive
      (fun s p => infiniteGibbsSpinMean beta v (fun i => X' i s p)) t ω) :
    let U := fun t ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))
    (∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P,
      |U p.1.toNNReal p.2| ≤ 2 * (T : ℝ) + 2 * (d : ℝ) * beta) ∧
    MemLp (fun p : ℝ × Ω => U p.1.toNNReal p.2) 2
      ((volume.restrict (Ioc (0 : ℝ) (T : ℝ))).prod P) := by
  dsimp only
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  have hm := isStronglyProgressive_infiniteGibbsSpinMean F beta v X hX
  have hm' := isStronglyProgressive_infiniteGibbsSpinMean F beta v X' hX'
  have hU : IsStronglyProgressive F (fun t ω =>
      Real.artanh (infiniteGibbsSpinMean beta v (fun i => X i t ω)) -
        Real.artanh (infiniteGibbsSpinMean beta v (fun i => X' i t ω))) := by
    intro t
    exact ((ha.comp (hm t).measurable).sub
      (ha.comp (hm' t).measurable)).stronglyMeasurable
  apply progressive_memLp_two_on_horizon hU T (2 * (T : ℝ) + 2 * (d : ℝ) * beta)
  intro t ht
  filter_upwards [hμ.gibbsField_copy_bound_of_shared_innovation hbeta
    hX hX' t v (hlaw t ht) (hlaw' t ht) (hx t ht) (hx' t ht)] with ω hω
  exact hω.trans (by have htr : (t : ℝ) ≤ T := ht; linarith)

end Problem367

end

end OAI
