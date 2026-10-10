import Mathlib
import OAI.Probability.SKFluctuations.ClockRetainedSamples

namespace OAI

/-! Clock Path Pair Measurable. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem monotoneOn_ae_continuous {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1)) :
    ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Icc (0:ℝ) 1 → ContinuousWithinAt q (Icc (0:ℝ) 1) u := by
  rw [ae_iff]
  simpa only [Classical.not_imp_iff_and_not,mem_ofPred_eq] using hq.countable_not_continuousWithinAt.measure_zero volume

 theorem sampledPairMoment_ae_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    ∀ᵐ u ∂volume.restrict (Ioc (0:ℝ) 1),
      Tendsto (fun n => stepPairMoment w φ (q 0) (sampleClockSteps q 0 (uniformMasses n))
        (sampleClockSteps_ordered q _ (uniformMasses_ordered n)).mem_pos P u)
        atTop (𝓝 (pathPairMoment w φ q P u)) := by
  have hm (i : ι) : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Icc (0:ℝ) 1 →
      ContinuousWithinAt (fun v => (q v i:ℝ)) (Icc (0:ℝ) 1) u :=
    monotoneOn_ae_continuous (fun u hu v hv huv => by exact_mod_cast hq i hu hv huv)
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [ae_all_iff.mpr hm] with u hc hu
  exact sampledPairMoment_tendsto hw φ D hD hφ q hq P hK hP hu (fun i => hc i ⟨hu.1.le,hu.2⟩)

 theorem pathPairMoment_aestronglyMeasurable {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    AEStronglyMeasurable (pathPairMoment w φ q P) (volume.restrict (Ioc (0:ℝ) 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop _
    (sampledPairMoment_ae_tendsto hw φ D hD hφ q hq P hK hP)
  intro n
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
    (stepPairMoment_intervalIntegrable w φ (q 0) (sampleClockSteps q 0 (uniformMasses n)) _ P 0 1)).aestronglyMeasurable

 theorem pathPairMoment_intervalIntegrable {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    IntervalIntegrable (pathPairMoment w φ q P) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  apply (integrable_const K).mono' (pathPairMoment_aestronglyMeasurable hw φ D hD hφ q hq P hK hP)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  simpa only [Real.norm_eq_abs] using pathPairMoment_bound hw φ D hD hφ q hq P hK hP hu

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 omit [Nonempty ι] in
 theorem clockCoordinateDistance_intervalIntegrable (D : ι → ℝ) (f g : ℝ → ι → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun u => f u i) volume 0 1)
    (hg : ∀ i, IntervalIntegrable (fun u => g u i) volume 0 1) :
    IntervalIntegrable (fun u => clockCoordinateDistance D (f u) (g u)) volume 0 1 := by
  have he : (fun u => clockCoordinateDistance D (f u) (g u)) =
      ∑ i, (fun u => |f u i-g u i| *(D i)^2) := by
    funext u
    simp only [clockCoordinateDistance,Finset.sum_apply]
  rw [he]
  exact IntervalIntegrable.sum Finset.univ (fun i _ => ((hf i).sub (hg i)).abs.mul_const ((D i)^2))

 theorem stepPairMoment_l1_path_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    (∫ u in (0:ℝ)..1, |stepPairMoment w φ q₀ L hL.mem_pos P u-pathPairMoment w φ q P u|) ≤
      ClockTree.errorJetVariation 2 0 0*K*(4*stepPathClockDistance D q₀ L q+
        clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) L L.length)
          (fun i => (q 1 i:ℝ))) := by
  have hf (i : ι) := stepClockFunction_intervalIntegrable (fun i => (q₀ i:ℝ)) hL i 0 1
  have hg (i : ι) : IntervalIntegrable (fun u => (q u i:ℝ)) volume 0 1 :=
    (show MonotoneOn (fun u => (q u i:ℝ)) (uIcc (0:ℝ) 1) from by
      rw [uIcc_of_le (by norm_num)]
      exact fun u hu v hv huv => by exact_mod_cast hq i hu hv huv).intervalIntegrable
  have hi := clockCoordinateDistance_intervalIntegrable D _ _ hf hg
  have hiP := (stepPairMoment_intervalIntegrable w φ q₀ L hL.mem_pos P 0 1).sub
    (pathPairMoment_intervalIntegrable hw φ D hD hφ q hq P hK hP)
  calc
    _ ≤ ∫ u in (0:ℝ)..1, ClockTree.errorJetVariation 2 0 0*K*(
        clockCoordinateDistance D (stepClockFunction (fun i => (q₀ i:ℝ)) L u)
          (fun i => (q u i:ℝ))+2*stepPathClockDistance D q₀ L q+
        clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) L L.length)
          (fun i => (q 1 i:ℝ))) :=
      intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hiP.abs
        ((hi.add intervalIntegrable_const).add intervalIntegrable_const |>.const_mul _)
        (fun u hu => stepPairMoment_path_comparison hw φ D hD hφ q₀ L hL q hq P hK hP ⟨hu.1,hu.2.le⟩)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (hi.add intervalIntegrable_const) intervalIntegrable_const,
        intervalIntegral.integral_add hi intervalIntegrable_const]
      simp only [intervalIntegral.integral_const,sub_zero,one_smul]
      rw [clockCoordinateDistance_integral D _ _ hf hg]
      unfold stepPathClockDistance
      simp only [Finset.mul_sum]
      congr 2
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

 theorem sampledPairMoment_l1_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {h : ℝ} (hm : PartitionMesh h 0 as)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    (∫ u in (0:ℝ)..1, |stepPairMoment w φ (q 0) (sampleClockSteps q 0 as)
      (sampleClockSteps_ordered q as ha).mem_pos P u-pathPairMoment w φ q P u|) ≤
      ClockTree.errorJetVariation 2 0 0*K*(4*h*clockVariationBound D q) := by
  have hb := stepPairMoment_l1_path_comparison hw φ D hD hφ (q 0)
    (sampleClockSteps q 0 as) (sampleClockSteps_ordered q as ha) q hq P hK hP
  simp only [sampleClockSteps_terminal q hq 0 as ha,he,clockCoordinateDistance,
    sub_self,abs_zero,zero_mul,Finset.sum_const_zero,add_zero] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ClockTree.errorJetVariation_nonneg _ _ _) hK)
  have hd := sample_stepPathClockDistance_le D q hq as ha hm
  linarith

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem disorderPressure_regularized_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq₀ : ∀ i, 0≤q 0 i)
    {ε : ℝ} (hε : 0≤ε) :
    |disorderPressure w φ C as 0 q 0-disorderPressure w φ C as 0 (regularizedClock q ε) 0| ≤
      (1/2:ℝ)*ε*(as.length+1)*(∑ i, (D i)^2) := by
  have hb := disorderPressure_comparison hw φ C D hself (fun i σ => hφ σ i)
    as ha.pairwise ha.members_le_one hq (regularizedClock_monotone q hq hε) hq₀
    (fun i => by dsimp [regularizedClock]; nlinarith [hq₀ i]) 0
  apply hb.trans
  have hi (i : ι) : rootBoundaryCost (as++[⟨1,by norm_num⟩])
      (fun j => q j i) (fun j => regularizedClock q ε j i) ≤ ε*(as.length+1) := by
    rw [rootBoundaryCost_eq_integral _ _ _ ha]
    simp_rw [massStepFunction_abs_sub]
    rw [massStepFunction_integral as 0 _ ha]
    have h (j : ℕ) (hj : j≤as.length) : |q j i-regularizedClock q ε j i|≤ε*(as.length+1) := by
      dsimp [regularizedClock]
      rw [sub_add_cancel_left,abs_neg,abs_of_nonneg (show 0≤ε*(j+1) by positivity)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hj 1) hε
    simpa only [massStepSum_const,sub_zero,one_mul] using massStepSum_mono as ha h
  calc
    _ ≤ (1/2:ℝ)*∑ i, (D i)^2*(ε*(as.length+1)) := by
      gcongr with i
      exact hi i
    _ = _ := by rw [←Finset.sum_mul]; ring

 def pressureRate (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q K : ℕ → ι → ℝ) : ℝ :=
  -(1/2:ℝ)*massStepSum as 0 (fun j => cumulativePair w φ as q j (featureKernel φ (K j)))

 theorem pressureRate_regularized_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q : ℕ → ι → ℝ) (hq : ∀ i, Monotone (fun j => q j i)) (hq₀ : ∀ i, 0≤q 0 i)
    (K : ℕ → ι → ℝ) {B : ℝ} (hB : 0≤B)
    (hK : ∀ j, j≤as.length → ∀ σ τ, |featureKernel φ (K j) σ τ|≤B)
    {ε : ℝ} (hε : 0≤ε) :
    |pressureRate w φ as q K-pressureRate w φ as (regularizedClock q ε) K| ≤
      (1/2:ℝ)*ClockTree.errorJetVariation 2 0 0*B*(3*ε*(as.length+1)*(∑ i, (D i)^2)) := by
  unfold pressureRate
  rw [←mul_sub,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2),←massStepSum_sub]
  rw [mul_assoc (1/2:ℝ),mul_assoc (1/2:ℝ)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact massStepSum_abs_bound as ha _ (fun j hj =>
    cumulativePair_regularized_bound hw φ D hD hφ as ha q hq hq₀ hε j _ hB (hK j hj))

 theorem disorderPressure_regularized_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq₀ : ∀ i, 0≤q 0 i) (hr₀ : ∀ i, 0≤r 0 i)
    {ε t : ℝ} (hε : 0<ε) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => disorderPressure w φ C as 0 (regularizedClock (affineCumulative q r s) ε) 0)
      (pressureRate w φ as (regularizedClock (affineCumulative q r t) ε) (fun j => r j-q j)) t := by
  have hd := disorderPressure_hasDerivAt hw φ C hself as ha (regularizedClock q ε) (regularizedClock r ε)
    ht (signedClockSteps_strict as _ _ (regularizedClock_strictMono q hq hε) (regularizedClock_strictMono r hr hε))
    (fun i => by
      rw [regularizedClock_affine]
      dsimp [regularizedClock]
      have h := affineCumulative_nonneg_zero q r hq₀ hr₀ ⟨ht.1.le,ht.2.le⟩ i
      norm_num
      linarith)
  simp_rw [regularizedClock_affine] at hd
  apply hd.congr_deriv
  unfold pressureRate cumulativePair
  congr 1
  congr 1
  funext j
  rw [ClockTree.pairDisorder_eq_rootLevelPairMean hw φ as ha, signedClockSteps_at,
    regularizedClock_affine]
  congr 2
  funext i
  simp only [regularizedClock,Pi.sub_apply]
  ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem disorderPressure_hasDerivAt_nonneg_bounded {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C D : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (hD : ∀ i, 0≤D i) (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq₀ : ∀ i, 0≤q 0 i) (hr₀ : ∀ i, 0≤r 0 i)
    {B : ℝ} (hB : 0≤B)
    (hK : ∀ j, j≤as.length → ∀ σ τ, |featureKernel φ (r j-q j) σ τ|≤B)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => disorderPressure w φ C as 0 (affineCumulative q r s) 0)
      (pressureRate w φ as (affineCumulative q r t) (fun j => r j-q j)) t := by
  let ε : ℕ → ℝ := fun n => ((n+1:ℕ):ℝ)⁻¹
  have hε (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  let A := (1/2:ℝ)*ClockTree.errorJetVariation 2 0 0*B*(3*(as.length+1)*(∑ i, (D i)^2))
  have hlim : Tendsto (fun n => ε n*A) atTop (𝓝 0) := by
    simpa [ε] using (uniformMasses_mesh_tendsto.mul_const A)
  have huni : TendstoUniformlyOn
      (fun n s => pressureRate w φ as (regularizedClock (affineCumulative q r s) (ε n)) (fun j => r j-q j))
      (fun s => pressureRate w φ as (affineCumulative q r s) (fun j => r j-q j)) atTop (Ioo (0:ℝ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn s hs
    rw [Real.dist_eq]
    apply (pressureRate_regularized_bound hw φ D hD hφ as ha _
      (affineCumulative_monotone q r hq hr ⟨hs.1.le,hs.2.le⟩)
      (affineCumulative_nonneg_zero q r hq₀ hr₀ ⟨hs.1.le,hs.2.le⟩)
      (fun j => r j-q j) hB hK (hε n).le).trans_lt
    convert hn using 1; dsimp [A]; ring
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo huni
    (Eventually.of_forall fun n s hs => disorderPressure_regularized_hasDerivAt
      hw φ C hself as ha q r hq hr hq₀ hr₀ (hε n) hs) _ ht
  intro s hs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => ?_)
    (show Tendsto (fun n => (1/2:ℝ)*ε n*(as.length+1)*(∑ i, (D i)^2)) atTop (𝓝 0) from by
      simpa [ε] using ((uniformMasses_mesh_tendsto.const_mul (1/2:ℝ)).mul_const ((as.length:ℝ)+1)).mul_const (∑ i, (D i)^2))
  rw [abs_sub_comm]
  exact disorderPressure_regularized_bound hw φ C D hself hφ as ha _
    (affineCumulative_monotone q r hq hr ⟨hs.1.le,hs.2.le⟩)
    (affineCumulative_nonneg_zero q r hq₀ hr₀ ⟨hs.1.le,hs.2.le⟩) (hε n).le

 theorem disorderPressure_hasDerivAt_nonneg {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (C : ι → ℝ)
    (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq₀ : ∀ i, 0≤q 0 i) (hr₀ : ∀ i, 0≤r 0 i)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => disorderPressure w φ C as 0 (affineCumulative q r s) 0)
      (pressureRate w φ as (affineCumulative q r t) (fun j => r j-q j)) t := by
  let D : ι → ℝ := fun i => ∑ σ, |φ σ (Pi.single i 1)|
  have hD : ∀ i, 0≤D i := by intro i; exact Finset.sum_nonneg (fun σ _ => abs_nonneg _)
  have hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i := by
    intro σ i
    dsimp [D]
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (φ τ (Pi.single i 1))) (Finset.mem_univ σ)
  let B : ℝ := ∑ j ∈ Finset.range (as.length+1), ∑ σ, ∑ τ, |featureKernel φ (r j-q j) σ τ|
  have hB : 0≤B := by dsimp [B]; positivity
  have hK (j : ℕ) (hj : j≤as.length) (σ τ : S) : |featureKernel φ (r j-q j) σ τ|≤B := by
    apply (Finset.single_le_sum (fun ρ _ => abs_nonneg (featureKernel φ (r j-q j) σ ρ)) (Finset.mem_univ τ)).trans
    apply (Finset.single_le_sum (fun ρ _ => Finset.sum_nonneg (fun η _ => abs_nonneg (featureKernel φ (r j-q j) ρ η))) (Finset.mem_univ σ)).trans
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ => abs_nonneg (featureKernel φ (r k-q k) σ τ))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact disorderPressure_hasDerivAt_nonneg_bounded hw φ C D hself hD hφ as ha q r hq hr hq₀ hr₀ hB hK ht

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 omit [Nonempty ι] in
 theorem ClockTree.expect_zeroShift_integrable {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ)
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (x : ι → ℝ) :
    Integrable (fun y => T.expect w φ q P (x+y)) ν := by
  simp_rw [T.expect_realize]
  exact ((T.realize q).expect_smooth hw φ (clockSteps_ordered ha q) _ 0).integrable_zero_shift x

 omit [Nonempty ι] in
 theorem ClockTree.disorderExpect_finsetSum {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    {κ : Type*} (s : Finset κ) (P : κ → T.Assignment → ℝ) (x : ι → ℝ) :
    T.disorderExpect w φ v q (fun σ => ∑ i ∈ s, P i σ) x=
      ∑ i ∈ s, T.disorderExpect w φ v q (P i) x := by
  simp_rw [T.disorderExpect_integral hw φ ha]
  have he (y : ι → ℝ) : T.expect w φ (cumulativeIncrements (q 0) (fun j => q (j+1)))
      (fun σ => ∑ i ∈ s, P i σ) y =
      ∑ i ∈ s, T.expect w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) (P i) y := by
    simp_rw [T.expect_realize]
    exact ReplicaTree.expect_finsetSum w φ _ s _ y
  simp_rw [zeroContinuation,he]
  exact integral_finsetSum s (fun i _ => T.expect_zeroShift_integrable hw φ ha _ (P i) _ x)

 omit [Nonempty ι] in
 theorem ClockTree.disorderExpect_const_mul {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) (c : ℝ) (x : ι → ℝ) :
    T.disorderExpect w φ v q (fun σ => c*P σ) x=c*T.disorderExpect w φ v q P x := by
  simp_rw [T.disorderExpect_integral hw φ ha,zeroContinuation,T.expect_realize,
    ReplicaTree.expect_const_mul]
  exact integral_const_mul _ _

 def coordinatePairTest (φ : S → (ι → ℝ) →L[ℝ] ℝ) (i : ι) (σ τ : S) : ℝ :=
  φ σ (Pi.single i 1)*φ τ (Pi.single i 1)

 omit [Nonempty ι] in
 theorem cumulativePair_featureKernel {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q : ℕ → ι → ℝ) (j : ℕ) (d : ι → ℝ) :
    cumulativePair w φ as q j (featureKernel φ d)=
      ∑ i, d i*cumulativePair w φ as q j (coordinatePairTest φ i) := by
  unfold cumulativePair featureKernel coordinatePairTest
  simp only [mul_assoc]
  rw [ClockTree.disorderExpect_finsetSum hw φ _ ha]
  simp_rw [ClockTree.disorderExpect_const_mul hw φ _ ha]

 theorem massStepFunction_mul (as : List PositiveMass) (f g : ℕ → ℝ) (u : ℝ) :
    massStepFunction as (fun j => f j*g j) u=massStepFunction as f u*massStepFunction as g u := by
  induction as generalizing f g with
  | nil => rfl
  | cons a as ih => simp only [massStepFunction]; split_ifs <;> simp_all

 theorem massStepFunction_sum {κ : Type*} (s : Finset κ) (as : List PositiveMass)
    (f : κ → ℕ → ℝ) (u : ℝ) :
    massStepFunction as (fun j => ∑ i ∈ s, f i j) u=∑ i ∈ s, massStepFunction as (f i) u := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
    simp only [massStepFunction]
    by_cases hu : u<a.val
    · simp only [ite_eq_left hu]
    · simp only [ite_eq_right hu,ih]

 omit [Nonempty ι] in
 theorem pressureRate_integral {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q K : ℕ → ι → ℝ) :
    pressureRate w φ as q K = -(1/2:ℝ)*∑ i, (∫ u in (0:ℝ)..1,
      massStepFunction as (fun j => K j i) u *
      massStepFunction as (fun j => cumulativePair w φ as q j (coordinatePairTest φ i)) u) := by
  unfold pressureRate
  simp_rw [cumulativePair_featureKernel hw φ as ha]
  rw [←massStepFunction_integral as 0 _ ha]
  simp_rw [massStepFunction_sum,massStepFunction_mul]
  congr 1
  rw [intervalIntegral.integral_finsetSum]
  intro i _
  rw [show (fun u => massStepFunction as (fun j => K j i) u *
    massStepFunction as (fun j => cumulativePair w φ as q j (coordinatePairTest φ i)) u)=
    massStepFunction as (fun j => K j i*cumulativePair w φ as q j (coordinatePairTest φ i)) from
      funext (fun u => (massStepFunction_mul _ _ _ _).symm)]
  exact massStepFunction_intervalIntegrable _ _ _ _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 @[simp] theorem partitionValues_zero (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) :
    partitionValues q a as 0=q a := by cases as <;> rfl

 def partitionPoint (a : ℝ) (as : List PositiveMass) (j : ℕ) : ℝ :=
  partitionValues id a as j

 theorem partitionValues_point (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) (j : ℕ) :
    partitionValues q a as j=q (partitionPoint a as j) := by
  induction as generalizing a j with
  | nil => rfl
  | cons b bs ih => cases j with
    | zero => rfl
    | succ j => exact ih b.val j

 theorem partitionPoint_mem {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as) (j : ℕ) :
    partitionPoint a as j ∈ Icc a 1 := by
  induction as generalizing a j with
  | nil => exact ⟨le_rfl,ha.2⟩
  | cons b bs ih => cases j with
    | zero => exact ⟨le_rfl,(massOrdered_bounds ha).2⟩
    | succ j =>
      have hh := ih ha.2.2 j
      exact ⟨ha.2.1.trans hh.1,hh.2⟩

 theorem partitionPoint_mono {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as) :
    Monotone (partitionPoint a as) := by
  apply monotone_nat_of_le_succ
  intro j
  induction as generalizing a j with
  | nil => exact le_rfl
  | cons b bs ih => cases j with
    | zero => simpa [partitionPoint,partitionValues] using ha.2.1
    | succ j => exact ih ha.2.2 j

 theorem partitionValues_mono {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1))
    {a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as) :
    Monotone (partitionValues q a as) := by
  intro j k hjk
  rw [partitionValues_point,partitionValues_point]
  have hj := partitionPoint_mem as ha j
  have hk := partitionPoint_mem as ha k
  exact hq ⟨(massOrdered_bounds ha).1.trans hj.1,hj.2⟩
    ⟨(massOrdered_bounds ha).1.trans hk.1,hk.2⟩ (partitionPoint_mono as ha hjk)

variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem sampledDisorderPressure_eq (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (x : ι → ℝ) :
    sampledDisorderPressure w φ C q as x = disorderPressure w φ C as 0
      (fun j i => (q (partitionPoint 0 as j) i:ℝ)) x := by
  unfold sampledDisorderPressure
  rw [stepDisorderPressure_eq w φ C (q 0) (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q as ha).mem_pos x,sampleClockSteps_masses]
  congr 1
  funext j i
  rw [sampleClockSteps_values q hq as ha,partitionValues_point]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
variable {ι S : Type*} [Fintype ι] [Fintype S]

 def affineClockPath (q r : ℝ → ι → ℝ≥0) (t : ℝ) (u : ℝ) (i : ι) : ℝ≥0 :=
  Real.toNNReal (1-t)*q u i+Real.toNNReal t*r u i

 omit [Fintype ι] in
 theorem affineClockPath_coe (q r : ℝ → ι → ℝ≥0) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (u : ℝ) (i : ι) :
    (affineClockPath q r t u i:ℝ)=(1-t)*(q u i:ℝ)+t*(r u i:ℝ) := by
  simp [affineClockPath,Real.toNNReal_of_nonneg ht.1,Real.toNNReal_of_nonneg (sub_nonneg.mpr ht.2)]

 omit [Fintype ι] in
 theorem affineClockPath_monotone (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1)) (t : ℝ) (i : ι) :
    MonotoneOn (fun u => affineClockPath q r t u i) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  exact add_le_add (mul_le_mul_of_nonneg_left (hq i hu hv huv) zero_le) (mul_le_mul_of_nonneg_left (hr i hu hv huv) zero_le)

 theorem affineClockPath_variation (D : ι → ℝ) (q r : ℝ → ι → ℝ≥0)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    clockVariationBound D (affineClockPath q r t)=
      (1-t)*clockVariationBound D q+t*clockVariationBound D r := by
  unfold clockVariationBound
  simp_rw [affineClockPath_coe q r ht]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

 theorem affineClockPath_variation_le (D : ι → ℝ) (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    clockVariationBound D (affineClockPath q r t) ≤ clockVariationBound D q+clockVariationBound D r := by
  rw [affineClockPath_variation D q r ht]
  have hq' := clockVariationBound_nonneg D q hq
  have hr' := clockVariationBound_nonneg D r hr
  exact add_le_add (mul_le_of_le_one_left hq' (by linarith [ht.1]))
    (mul_le_of_le_one_left hr' ht.2)

 theorem sampledAffinePressure_hasDerivAt [Nonempty S] [Nonempty ι]
    {w : S → ℝ} (hw : ∀ σ, 0<w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (hself : ∀ σ i, (φ σ (Pi.single i 1))^2=C i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => sampledDisorderPressure w φ C (affineClockPath q r s) as 0)
      (pressureRate w φ as (fun j i => (affineClockPath q r t (partitionPoint 0 as j) i:ℝ))
        (fun j i => (r (partitionPoint 0 as j) i:ℝ)-(q (partitionPoint 0 as j) i:ℝ))) t := by
  let Q : ℕ → ι → ℝ := fun j i => (q (partitionPoint 0 as j) i:ℝ)
  let R : ℕ → ι → ℝ := fun j i => (r (partitionPoint 0 as j) i:ℝ)
  have hQ (i : ι) : Monotone (fun j => Q j i) := by
    intro j k hjk
    exact_mod_cast hq i (partitionPoint_mem as ha j) (partitionPoint_mem as ha k) (partitionPoint_mono as ha hjk)
  have hR (i : ι) : Monotone (fun j => R j i) := by
    intro j k hjk
    exact_mod_cast hr i (partitionPoint_mem as ha j) (partitionPoint_mem as ha k) (partitionPoint_mono as ha hjk)
  have he (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      (fun j i => (affineClockPath q r s (partitionPoint 0 as j) i:ℝ))=affineCumulative Q R s := by
    funext j i
    rw [affineClockPath_coe q r hs]
    dsimp [affineCumulative,Q,R]
    ring
  rw [he t ⟨ht.1.le,ht.2.le⟩]
  apply (disorderPressure_hasDerivAt_nonneg hw φ C hself as ha Q R hQ hR
    (fun i => NNReal.coe_nonneg _) (fun i => NNReal.coe_nonneg _) ht).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  rw [sampledDisorderPressure_eq w φ C _ (affineClockPath_monotone q r hq hr s) as ha,he s ⟨hs.1.le,hs.2.le⟩]

end SKFluctuations.Hierarchy

end

end OAI
