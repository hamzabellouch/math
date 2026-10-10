import Mathlib
import OAI.Probability.SKFluctuations.ClockPathPairMeasurable

namespace OAI

/-! Clock Sampled Rate. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty S] in
 theorem sampledPairMoment_eq (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (P : S → S → ℝ) (u : ℝ) :
    stepPairMoment w φ (q 0) (sampleClockSteps q 0 as) (sampleClockSteps_ordered q as ha).mem_pos P u=
      massStepFunction as (fun j => cumulativePair w φ as
        (fun j i => (q (partitionPoint 0 as j) i:ℝ)) j P) u := by
  unfold stepPairMoment
  rw [sampleClockSteps_masses]
  congr 2
  funext j
  congr 2
  funext k i
  rw [sampleClockSteps_values q hq as ha,partitionValues_point]

 theorem massStepFunction_sub (as : List PositiveMass) (f g : ℕ → ℝ) (u : ℝ) :
    massStepFunction as (fun j => f j-g j) u=massStepFunction as f u-massStepFunction as g u := by
  induction as generalizing f g with
  | nil => rfl
  | cons a as ih => simp only [massStepFunction]; split_ifs <;> simp_all

 theorem sampledPressureRate_integral {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (K : ℝ → ι → ℝ) (as : List PositiveMass) (ha : MassOrdered 0 as) :
    pressureRate w φ as (fun j i => (q (partitionPoint 0 as j) i:ℝ))
      (fun j i => K (partitionPoint 0 as j) i)=
      -(1/2:ℝ)*∑ i, ∫ u in (0:ℝ)..1,
        partitionSample (fun v => K v i) 0 as u *
        stepPairMoment w φ (q 0) (sampleClockSteps q 0 as)
          (sampleClockSteps_ordered q as ha).mem_pos (coordinatePairTest φ i) u := by
  rw [pressureRate_integral hw φ as ha]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [sampledPairMoment_eq w φ q hq as ha]
  congr 1
  unfold partitionSample
  congr 1
  funext j
  exact (partitionValues_point (fun v => K v i) 0 as j).symm

 omit [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι] in
 theorem coordinatePairTest_bound (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i) (i : ι) (σ τ : S) :
    |coordinatePairTest φ i σ τ|≤(D i)^2 := by
  unfold coordinatePairTest
  rw [abs_mul,pow_two]
  exact mul_le_mul (hφ σ i) (hφ τ i) (abs_nonneg _) ((abs_nonneg _).trans (hφ σ i))

 omit [Fintype ι] [Nonempty ι] in
 theorem clockDirection_bound (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (i : ι) :
    |(r u i:ℝ)-(q u i:ℝ)|≤(r 1 i:ℝ)+(q 1 i:ℝ) := by
  apply (abs_sub _ _).trans
  simp only [abs_of_nonneg (NNReal.coe_nonneg _)]
  exact add_le_add (by exact_mod_cast hr i hu (by constructor <;> norm_num) hu.2)
    (by exact_mod_cast hq i hu (by constructor <;> norm_num) hu.2)

 theorem partitionSample_sub (q r : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) (u : ℝ) :
    partitionSample (fun v => r v-q v) a as u=partitionSample r a as u-partitionSample q a as u := by
  rw [partitionSample_comp (fun v => r v-q v),partitionSample_comp r,partitionSample_comp q]

 omit [Fintype ι] [Nonempty ι] in
 theorem clockDirection_intervalIntegrable (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1)) (i : ι) :
    IntervalIntegrable (fun u => (r u i:ℝ)-(q u i:ℝ)) volume 0 1 := by
  have hi (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1)) :
      IntervalIntegrable (fun u => (p u i:ℝ)) volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact fun u hu v hv huv => by exact_mod_cast hp i hu hv huv
  exact (hi r hr).sub (hi q hq)

 omit [Fintype ι] [Nonempty ι] in
 theorem sampledClockDirection_l1_bound (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as) (i : ι) :
    (∫ u in (0:ℝ)..1, |partitionSample (fun v => (r v i:ℝ)-(q v i:ℝ)) 0 as u-
      ((r u i:ℝ)-(q u i:ℝ))|) ≤ h*((r 1 i:ℝ)-(r 0 i:ℝ)+((q 1 i:ℝ)-(q 0 i:ℝ))) := by
  have hi (p : ℝ → ι → ℝ≥0) (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1)) :
      IntervalIntegrable (fun u => (p u i:ℝ)) volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num)]
    exact fun u hu v hv huv => by exact_mod_cast hp i hu hv huv
  have hiq := ((partitionSample_intervalIntegrable (fun u => (q u i:ℝ)) 0 as 0 1).sub (hi q hq)).abs
  have hir := ((partitionSample_intervalIntegrable (fun u => (r u i:ℝ)) 0 as 0 1).sub (hi r hr)).abs
  calc
    _ ≤ ∫ u in (0:ℝ)..1, |partitionSample (fun v => (r v i:ℝ)) 0 as u-(r u i:ℝ)|+
        |partitionSample (fun v => (q v i:ℝ)) 0 as u-(q u i:ℝ)| := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
        ((partitionSample_intervalIntegrable _ _ _ _ _).sub (clockDirection_intervalIntegrable q r hq hr i)).abs (hir.add hiq)
      intro u _
      rw [partitionSample_sub]
      convert abs_sub (partitionSample (fun v => (r v i:ℝ)) 0 as u-(r u i:ℝ))
        (partitionSample (fun v => (q v i:ℝ)) 0 as u-(q u i:ℝ)) using 1; congr 1; ring
    _ = (∫ u in (0:ℝ)..1, |partitionSample (fun v => (r v i:ℝ)) 0 as u-(r u i:ℝ)|)+
        (∫ u in (0:ℝ)..1, |partitionSample (fun v => (q v i:ℝ)) 0 as u-(q u i:ℝ)|) :=
      intervalIntegral.integral_add hir hiq
    _ ≤ _ := by
      have hbq := partitionSample_l1_error (fun u hu v hv huv => show (q u i:ℝ)≤(q v i:ℝ) by exact_mod_cast hq i hu hv huv) as ha hm
      have hbr := partitionSample_l1_error (fun u hu v hv huv => show (r u i:ℝ)≤(r v i:ℝ) by exact_mod_cast hr i hu hv huv) as ha hm
      simpa only [abs_sub_comm,mul_add] using add_le_add hbr hbq

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem intervalIntegrable_mul_bounded {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    {K : ℝ} (hK : ∀ u ∈ Ioc (0:ℝ) 1, |g u|≤K) :
    IntervalIntegrable (fun u => f u*g u) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at hf hg ⊢
  apply hf.mul_bdd hg.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa only [Real.norm_eq_abs] using hK u hu

 theorem integral_product_error_le {f g fn gn : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
    (hfn : IntervalIntegrable fn volume 0 1) (hgn : IntervalIntegrable gn volume 0 1)
    {M K : ℝ} (hM : ∀ u ∈ Ioc (0:ℝ) 1, |f u|≤M)
    (hK : ∀ u ∈ Ioc (0:ℝ) 1, |gn u|≤K) :
    |(∫ u in (0:ℝ)..1, fn u*gn u)-(∫ u in (0:ℝ)..1, f u*g u)| ≤
      M*(∫ u in (0:ℝ)..1, |gn u-g u|)+K*(∫ u in (0:ℝ)..1, |fn u-f u|) := by
  have hin := intervalIntegrable_mul_bounded hfn hgn hK
  have hi : IntervalIntegrable (fun u => f u*g u) volume 0 1 := by
    simpa only [mul_comm] using intervalIntegrable_mul_bounded hg hf hM
  rw [←intervalIntegral.integral_sub hin hi]
  apply (show |∫ u in (0:ℝ)..1, fn u*gn u-f u*g u| ≤
    ∫ u in (0:ℝ)..1, |fn u*gn u-f u*g u| from by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := fun u => fn u*gn u-f u*g u) (by norm_num : (0:ℝ)≤1)).trans
  calc
    _ ≤ ∫ u in (0:ℝ)..1, M*|gn u-g u|+K*|fn u-f u| := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) (hin.sub hi).abs
        (((hgn.sub hg).abs.const_mul M).add ((hfn.sub hf).abs.const_mul K))
      intro u hu
      have hu' : u ∈ Ioc (0:ℝ) 1 := ⟨hu.1,hu.2.le⟩
      calc
        _ = |f u*(gn u-g u)+(fn u-f u)*gn u| := by congr 1; ring
        _ ≤ |f u*(gn u-g u)|+|(fn u-f u)*gn u| := abs_add_le _ _
        _ = |f u| *|gn u-g u|+|gn u| *|fn u-f u| := by rw [abs_mul,abs_mul]; ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hM u hu') (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hK u hu') (abs_nonneg _))
    _ = _ := by
      rw [intervalIntegral.integral_add ((hgn.sub hg).abs.const_mul M) ((hfn.sub hf).abs.const_mul K),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem sampledRateCoordinate_error {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (p q r : ℝ → ι → ℝ≥0)
    (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {h : ℝ} (hm : PartitionMesh h 0 as) (i : ι) :
    |(∫ u in (0:ℝ)..1, partitionSample (fun v => (r v i:ℝ)-(q v i:ℝ)) 0 as u *
        stepPairMoment w φ (p 0) (sampleClockSteps p 0 as)
          (sampleClockSteps_ordered p as ha).mem_pos (coordinatePairTest φ i) u)-
      (∫ u in (0:ℝ)..1, ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p (coordinatePairTest φ i) u)| ≤
      ((r 1 i:ℝ)+(q 1 i:ℝ))*(ClockTree.errorJetVariation 2 0 0*(D i)^2*(4*h*clockVariationBound D p))+
        (D i)^2*(h*((r 1 i:ℝ)-(r 0 i:ℝ)+((q 1 i:ℝ)-(q 0 i:ℝ)))) := by
  have htest := coordinatePairTest_bound φ D hφ i
  have hi := integral_product_error_le (clockDirection_intervalIntegrable q r hq hr i)
    (pathPairMoment_intervalIntegrable hw φ D hD hφ p hp _ (sq_nonneg _) htest)
    (partitionSample_intervalIntegrable (fun v => (r v i:ℝ)-(q v i:ℝ)) 0 as 0 1)
    (stepPairMoment_intervalIntegrable w φ (p 0) (sampleClockSteps p 0 as)
      (sampleClockSteps_ordered p as ha).mem_pos (coordinatePairTest φ i) 0 1)
    (fun u hu => clockDirection_bound q r hq hr ⟨hu.1.le,hu.2⟩ i)
    (fun u _ => stepPairMoment_bound hw φ (p 0) _ (sampleClockSteps_ordered p as ha) _ htest u)
  apply hi.trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left (sampledPairMoment_l1_bound hw φ D hD hφ p hp as ha he hm _ (sq_nonneg _) htest)
      (add_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)))
    (mul_le_mul_of_nonneg_left (sampledClockDirection_l1_bound q r hq hr as ha hm i) (sq_nonneg _))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 def pathPressureRate (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (p : ℝ → ι → ℝ≥0) (K : ℝ → ι → ℝ) : ℝ :=
  -(1/2:ℝ)*∑ i, ∫ u in (0:ℝ)..1, K u i*pathPairMoment w φ p (coordinatePairTest φ i) u

 def pathRateApproxConstant (D : ι → ℝ) (q r : ℝ → ι → ℝ≥0) : ℝ :=
  (1/2:ℝ)*(∑ i, (((r 1 i:ℝ)+(q 1 i:ℝ))*ClockTree.errorJetVariation 2 0 0*(D i)^2*4*
    (clockVariationBound D q+clockVariationBound D r)+
    (D i)^2*((r 1 i:ℝ)-(r 0 i:ℝ)+((q 1 i:ℝ)-(q 0 i:ℝ)))))

 theorem sampledAffineRate_error {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {h : ℝ} (hh : 0≤h) (hm : PartitionMesh h 0 as)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    |pressureRate w φ as (fun j i => (affineClockPath q r t (partitionPoint 0 as j) i:ℝ))
        (fun j i => (r (partitionPoint 0 as j) i:ℝ)-(q (partitionPoint 0 as j) i:ℝ))-
      pathPressureRate w φ (affineClockPath q r t) (fun u i => (r u i:ℝ)-(q u i:ℝ))| ≤
      h*pathRateApproxConstant D q r := by
  let p := affineClockPath q r t
  have hp := affineClockPath_monotone q r hq hr t
  rw [sampledPressureRate_integral hw φ _ hp (fun u i => (r u i:ℝ)-(q u i:ℝ)) as ha]
  unfold pathPressureRate
  rw [←mul_sub,abs_mul,←Finset.sum_sub_distrib]
  norm_num only [abs_neg,abs_div,abs_one,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num : (0:ℝ)≤1/2)).trans
  calc
    _ ≤ (1/2:ℝ)*∑ i, h*(((r 1 i:ℝ)+(q 1 i:ℝ))*ClockTree.errorJetVariation 2 0 0*(D i)^2*4*
        (clockVariationBound D q+clockVariationBound D r)+
        (D i)^2*((r 1 i:ℝ)-(r 0 i:ℝ)+((q 1 i:ℝ)-(q 0 i:ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i _
      apply (sampledRateCoordinate_error hw φ D hD hφ p q r hp hq hr as ha he hm i).trans
      have hv := mul_le_mul_of_nonneg_left (affineClockPath_variation_le D q r hq hr ht)
        (show 0≤((r 1 i:ℝ)+(q 1 i:ℝ))*ClockTree.errorJetVariation 2 0 0*(D i)^2*(4*h) from by
          apply mul_nonneg
          · exact mul_nonneg (mul_nonneg (add_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
              (ClockTree.errorJetVariation_nonneg _ _ _)) (sq_nonneg _)
          · positivity)
      dsimp [p]
      nlinarith only [hv]
    _ = _ := by rw [←Finset.mul_sum]; unfold pathRateApproxConstant; ring

 theorem pathDisorderPressure_hasDerivAt_bounded {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hD : ∀ i, 0≤D i) (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => pathDisorderPressure w φ C (affineClockPath q r s) 0)
      (pathPressureRate w φ (affineClockPath q r t) (fun u i => (r u i:ℝ)-(q u i:ℝ))) t := by
  have hlim : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹*pathRateApproxConstant D q r) atTop (𝓝 0) := by
    simpa using uniformMasses_mesh_tendsto.mul_const (pathRateApproxConstant D q r)
  have huni : TendstoUniformlyOn
      (fun n s => pressureRate w φ (uniformMasses n)
        (fun j i => (affineClockPath q r s (partitionPoint 0 (uniformMasses n) j) i:ℝ))
        (fun j i => (r (partitionPoint 0 (uniformMasses n) j) i:ℝ)-(q (partitionPoint 0 (uniformMasses n) j) i:ℝ)))
      (fun s => pathPressureRate w φ (affineClockPath q r s) (fun u i => (r u i:ℝ)-(q u i:ℝ))) atTop (Ioo (0:ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn s hs
    rw [Real.dist_eq,abs_sub_comm]
    exact (sampledAffineRate_error hw φ D hD hφ q r hq hr (uniformMasses n)
      (uniformMasses_ordered n) (uniformMasses_end n) (by positivity) (uniformMasses_mesh n) ⟨hs.1.le,hs.2.le⟩).trans_lt hn
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo huni
    (Eventually.of_forall fun n s hs => sampledAffinePressure_hasDerivAt hw φ C hself q r hq hr
      (uniformMasses n) (uniformMasses_ordered n) hs) _ ht
  intro s hs
  exact sampledDisorderPressure_tendsto hw φ C D hself (fun i σ => hφ σ i)
    (affineClockPath q r s) (affineClockPath_monotone q r hq hr s) 0

 theorem pathDisorderPressure_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => pathDisorderPressure w φ C (affineClockPath q r s) 0)
      (pathPressureRate w φ (affineClockPath q r t) (fun u i => (r u i:ℝ)-(q u i:ℝ))) t := by
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  exact pathDisorderPressure_hasDerivAt_bounded hw φ C D hself hD hφ q r hq hr ht

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem stepPairDisorder_finsetSum {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ≥0)
    (A B : List (GaussianStep ι)) (ho : OrderedSteps 0 (A++B))
    {κ : Type*} (s : Finset κ) (P : κ → S → S → ℝ) (x : ι → ℝ) :
    stepPairDisorder w φ v A B (fun σ τ => ∑ i ∈ s, P i σ τ) x=
      ∑ i ∈ s, stepPairDisorder w φ v A B (P i) x := by
  have hA : ∀ t ∈ A, 0<t.1 := fun t ht => ho.mem_pos t (List.mem_append_left _ ht)
  have hB : ∀ t ∈ B, 0<t.1 := fun t ht => ho.mem_pos t (List.mem_append_right _ ht)
  have ha : MassOrdered 0 (positiveStepMasses A hA++positiveStepMasses B hB) := by
    rw [←positiveStepMasses_append]
    exact positiveStepMasses_ordered ho _
  have he (P : S → S → ℝ) := congr_fun (ClockTree.pairDisorder_coordinates hw φ A B hA hB ho v P) x
  simp_rw [←he]
  exact ClockTree.disorderExpect_finsetSum hw φ _ ha _ _ s _ x

 omit [Nonempty ι] in
 theorem stepPairDisorder_const_mul {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ≥0)
    (A B : List (GaussianStep ι)) (ho : OrderedSteps 0 (A++B))
    (P : S → S → ℝ) (c : ℝ) (x : ι → ℝ) :
    stepPairDisorder w φ v A B (fun σ τ => c*P σ τ) x=
      c*stepPairDisorder w φ v A B P x := by
  have hA : ∀ t ∈ A, 0<t.1 := fun t ht => ho.mem_pos t (List.mem_append_left _ ht)
  have hB : ∀ t ∈ B, 0<t.1 := fun t ht => ho.mem_pos t (List.mem_append_right _ ht)
  have ha : MassOrdered 0 (positiveStepMasses A hA++positiveStepMasses B hB) := by
    rw [←positiveStepMasses_append]
    exact positiveStepMasses_ordered ho _
  have he (P : S → S → ℝ) := congr_fun (ClockTree.pairDisorder_coordinates hw φ A B hA hB ho v P) x
  simp_rw [←he]
  exact ClockTree.disorderExpect_const_mul hw φ _ ha _ _ _ c x

 omit [Fintype ι] [Nonempty ι] in
 theorem retainedPairSample_ordered (q : ℝ → ι → ℝ≥0) (u : PositiveMass) (hu : u.val≤1)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    OrderedSteps 0 ((sampleClockSteps q 0 (retainedBefore u as))++
      sampleClockSteps q u.val (retainedAfter u as)) := by
  have ho := retainedMasses_ordered u hu as ha
  exact (sampleClockSteps_ordered q _ ho.1).append_bound u.property.le
    (sampleClockSteps_mass_le q _ _ (retainedBefore_bounds u _)) (sampleClockSteps_ordered q _ ho.2)

 theorem retainedPairSample_tendsto_all {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (P : S → S → ℝ) (x : ι → ℝ) :
    Tendsto (fun k => retainedPairSample w φ q u (uniformMasses k) P x) atTop
      (𝓝 (pathPairDisorder w φ q u P x)) := by
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  let K : ℝ := ∑ σ, ∑ τ, |P σ τ|
  have hK : 0≤K := by dsimp [K]; positivity
  have hP (σ τ : S) : |P σ τ|≤K := by
    exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  exact retainedPairSample_tendsto hw φ D hD hφ q hq u hu P hK hP x

 theorem pathPairMoment_finsetSum {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {κ : Type*} (s : Finset κ) (P : κ → S → S → ℝ)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q (fun σ τ => ∑ i ∈ s, P i σ τ) u=
      ∑ i ∈ s, pathPairMoment w φ q (P i) u := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  have he (n : ℕ) : retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses n) (fun σ τ => ∑ i ∈ s, P i σ τ) 0=
      ∑ i ∈ s, retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses n) (P i) 0 :=
    stepPairDisorder_finsetSum hw φ _ _ _ (retainedPairSample_ordered q ⟨u,hu.1⟩ hu.2 _ (uniformMasses_ordered n)) s P 0
  apply tendsto_nhds_unique (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 _ 0)
  simp_rw [he]
  exact tendsto_finsetSum s (fun i _ => retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 (P i) 0)

 theorem pathPairMoment_const_mul {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) (c : ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q (fun σ τ => c*P σ τ) u=c*pathPairMoment w φ q P u := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  have he (n : ℕ) : retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses n) (fun σ τ => c*P σ τ) 0=
      c*retainedPairSample w φ q ⟨u,hu.1⟩ (uniformMasses n) P 0 :=
    stepPairDisorder_const_mul hw φ _ _ _ (retainedPairSample_ordered q ⟨u,hu.1⟩ hu.2 _ (uniformMasses_ordered n)) P c 0
  apply tendsto_nhds_unique (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 _ 0)
  simp_rw [he]
  exact (retainedPairSample_tendsto_all hw φ q hq ⟨u,hu.1⟩ hu.2 P 0).const_mul c

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathPairMoment_add {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P Q : S → S → ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q (fun σ τ => P σ τ+Q σ τ) u=
      pathPairMoment w φ q P u+pathPairMoment w φ q Q u := by
  have he := pathPairMoment_finsetSum hw φ q hq Finset.univ
    (fun b : Bool => if b then P else Q) hu
  simpa using he

 theorem pathPairMoment_intervalIntegrable_all {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1)) (P : S → S → ℝ) :
    IntervalIntegrable (pathPairMoment w φ q P) volume 0 1 := by
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg fun σ _ => abs_nonneg _
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  let K : ℝ := ∑ σ, ∑ τ, |P σ τ|
  have hK : 0≤K := by dsimp [K]; positivity
  have hP (σ τ : S) : |P σ τ|≤K := by
    exact (Finset.single_le_sum (fun ρ _ => abs_nonneg (P σ ρ)) (Finset.mem_univ τ)).trans
      (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg fun η _ => abs_nonneg (P ρ η)) (Finset.mem_univ σ))
  exact pathPairMoment_intervalIntegrable hw φ D hD hφ q hq P hK hP

 theorem pathPairMoment_featureKernel {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (K : ι → ℝ) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    pathPairMoment w φ q (featureKernel φ K) u=
      ∑ i, K i*pathPairMoment w φ q (coordinatePairTest φ i) u := by
  have he : featureKernel φ K = fun σ τ => ∑ i, K i*coordinatePairTest φ i σ τ := by
    funext σ τ; simp only [featureKernel,coordinatePairTest]; congr 1; funext i; ring
  rw [he,pathPairMoment_finsetSum hw φ q hq Finset.univ _ hu]
  apply Finset.sum_congr rfl
  intro i _
  exact pathPairMoment_const_mul hw φ q hq _ (K i) hu

 theorem pathPressureRate_integral {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (p q r : ℝ → ι → ℝ≥0)
    (hp : ∀ i, MonotoneOn (fun u => p u i) (Icc (0:ℝ) 1))
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1)) :
    pathPressureRate w φ p (fun u i => (r u i:ℝ)-(q u i:ℝ))=
      -(1/2:ℝ)*∫ u in (0:ℝ)..1,
        pathPairMoment w φ p (featureKernel φ (fun i => (r u i:ℝ)-(q u i:ℝ))) u := by
  have hi (i : ι) : IntervalIntegrable
      (fun u => ((r u i:ℝ)-(q u i:ℝ))*pathPairMoment w φ p (coordinatePairTest φ i) u) volume 0 1 := by
    simpa only [mul_comm] using intervalIntegrable_mul_bounded
      (pathPairMoment_intervalIntegrable_all hw φ p hp _) (clockDirection_intervalIntegrable q r hq hr i)
      (fun u hu => clockDirection_bound q r hq hr ⟨hu.1.le,hu.2⟩ i)
  unfold pathPressureRate
  rw [←intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with u hu
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
  exact (pathPairMoment_featureKernel hw φ p hp _ hu).symm

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 omit [Nonempty ι] in
 theorem clockCoordinateDistance_le (D C : ι → ℝ) (q r : ι → ℝ)
    (h : ∀ i, |q i-r i|≤C i) :
    clockCoordinateDistance D q r≤∑ i, C i*(D i)^2 := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (h i) (sq_nonneg _)

 theorem sampledPairDisorder_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D C : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤C i)
    (u : PositiveMass) (hu : u.val≤1) (as bs : List PositiveMass)
    (ha : MassOrdered 0 as) (hb : MassOrdered u.val bs) (hau : ∀ a ∈ as, a.val≤u.val)
    (heA : partitionEnd 0 as=u.val) (heB : partitionEnd u.val bs=1)
    {m : ℝ} (hm : PartitionMesh m 0 (as++bs))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |sampledPairDisorder w φ q u.val as bs P x-sampledPairDisorder w φ r u.val as bs P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*(3*∑ i, C i*(D i)^2) := by
  have hoa : MassOrdered 0 (as++bs) := ha.append_end (heA.symm ▸ hb)
  have he : partitionEnd 0 (as++bs)=1 := by rw [partitionEnd_append,heA,heB]
  have hAB (p : ℝ → ι → ℝ≥0) : sampleClockSteps p 0 as++sampleClockSteps p u.val bs=
      sampleClockSteps p 0 (as++bs) := by rw [sampleClockSteps_append,heA]
  have hh := stepPairDisorder_l1_comparison hw φ D hD hφ (q 0) (r 0)
    (sampleClockSteps q 0 as) (sampleClockSteps q u.val bs)
    (sampleClockSteps r 0 as) (sampleClockSteps r u.val bs) u.property.le
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb)
    (sampleClockSteps_ordered r as ha) (sampleClockSteps_ordered r bs hb)
    (sampleClockSteps_mass_le q 0 as hau) (sampleClockSteps_mass_le r 0 as hau) P hK hP x
  rw [sampleClockSteps_terminal q hq 0 as ha,sampleClockSteps_terminal r hr 0 as ha,heA,
    hAB q,hAB r,sampleClockSteps_terminal q hq 0 (as++bs) hoa,
    sampleClockSteps_terminal r hr 0 (as++bs) hoa,he] at hh
  have hi := clockCoordinateDistance_intervalIntegrable D
    (stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as++bs)))
    (stepClockFunction (fun i => (r 0 i:ℝ)) (sampleClockSteps r 0 (as++bs)))
    (fun i => stepClockFunction_intervalIntegrable _ (sampleClockSteps_ordered q _ hoa) i 0 1)
    (fun i => stepClockFunction_intervalIntegrable _ (sampleClockSteps_ordered r _ hoa) i 0 1)
  have hiB : (∫ v in (0:ℝ)..1, clockCoordinateDistance D
      (stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as++bs)) v)
      (stepClockFunction (fun i => (r 0 i:ℝ)) (sampleClockSteps r 0 (as++bs)) v))≤∑ i, C i*(D i)^2 := by
    calc
      _ ≤ ∫ v in (0:ℝ)..1, ∑ i, C i*(D i)^2 := by
        apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi intervalIntegrable_const
        intro v hv
        apply clockCoordinateDistance_le
        intro i
        rw [sampleClockSteps_function q hq _ hoa v i,sampleClockSteps_function r hr _ hoa v i,
          partitionSample_comp (fun v => (q v i:ℝ)),partitionSample_comp (fun v => (r v i:ℝ))]
        have hB := partitionSample_id_bounds (as++bs) hoa hm ⟨hv.1.le,hv.2.le⟩
        exact hC _ ⟨hB.1,hB.2.1.trans hv.2.le⟩ i
      _ = _ := by simp
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ClockTree.errorJetVariation_nonneg _ _ _) hK)
  have hf := clockCoordinateDistance_le D C _ _ (hC u.val ⟨u.property.le,hu⟩)
  have ht := clockCoordinateDistance_le D C _ _ (hC 1 (by constructor <;> norm_num))
  linarith

 theorem retainedPairSample_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D C : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤C i)
    (u : PositiveMass) (hu : u.val≤1) (k : ℕ)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |retainedPairSample w φ q u (uniformMasses k) P x-retainedPairSample w φ r u (uniformMasses k) P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*(3*∑ i, C i*(D i)^2) := by
  have ho := retainedMasses_ordered u hu (uniformMasses k) (uniformMasses_ordered k)
  exact sampledPairDisorder_sup_comparison hw φ D C hD hφ q r hq hr hC u hu _ _ ho.1 ho.2
    (retainedBefore_bounds u _) (retainedBefore_end u _) (retainedAfter_end u _)
    (retainedMasses_mesh u hu _ (uniformMasses_ordered k) (by positivity) (uniformMasses_mesh k)) P hK hP x

 theorem pathPairDisorder_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D C : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤C i)
    (u : PositiveMass) (hu : u.val≤1)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |pathPairDisorder w φ q u P x-pathPairDisorder w φ r u P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*(3*∑ i, C i*(D i)^2) := by
  apply le_of_tendsto ((retainedPairSample_tendsto_all hw φ q hq u hu P x).sub
    (retainedPairSample_tendsto_all hw φ r hr u hu P x)).abs
  exact Eventually.of_forall fun k => retainedPairSample_sup_comparison hw φ D C hD hφ q r hq hr hC u hu k P hK hP x

 theorem pathPairMoment_sup_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D C : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (hC : ∀ u ∈ Icc (0:ℝ) 1, ∀ i, |(q u i:ℝ)-(r u i:ℝ)|≤C i)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    |pathPairMoment w φ q P u-pathPairMoment w φ r P u| ≤
      ClockTree.errorJetVariation 2 0 0*K*(3*∑ i, C i*(D i)^2) := by
  simp only [pathPairMoment,dite_eq_left hu.1]
  exact pathPairDisorder_sup_comparison hw φ D C hD hφ q r hq hr hC ⟨u,hu.1⟩ hu.2 P hK hP 0

end SKFluctuations.Hierarchy

end

end OAI
