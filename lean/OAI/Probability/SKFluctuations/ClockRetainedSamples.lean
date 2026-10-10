import Mathlib
import OAI.Probability.SKFluctuations.ClockSplitSteps

namespace OAI

/-! Clock Retained Samples. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def retainedBefore (u : PositiveMass) (as : List PositiveMass) : List PositiveMass :=
  (splitMassPartition u as).1
 def retainedAfter (u : PositiveMass) (as : List PositiveMass) : List PositiveMass :=
  (splitMassPartition u as).2++[⟨1,by norm_num⟩]

 theorem retainedBefore_end (u : PositiveMass) (as : List PositiveMass) :
    partitionEnd 0 (retainedBefore u as)=u.val := splitMassPartition_end _ _ _
 theorem retainedAfter_end (u : PositiveMass) (as : List PositiveMass) :
    partitionEnd u.val (retainedAfter u as)=1 := by
  rw [retainedAfter,partitionEnd_append]
  rfl
 theorem retainedBefore_bounds (u : PositiveMass) (as : List PositiveMass) :
    ∀ a ∈ retainedBefore u as, a.val≤u.val := splitMassPartition_bounds _ _
 theorem retainedMasses_ordered (u : PositiveMass) (hu : u.val≤1)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    MassOrdered 0 (retainedBefore u as) ∧ MassOrdered u.val (retainedAfter u as) := by
  have ho := splitMassPartition_ordered u hu as ha u.property.le
  exact ⟨ho.1,ho.2.append_end ⟨ho.2.end_bounds.1,ho.2.end_bounds.2,by norm_num,by norm_num⟩⟩
 theorem retainedMasses_mesh (u : PositiveMass) (hu : u.val≤1)
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hh : 0≤h)
    (hm : PartitionMesh h 0 as) :
    PartitionMesh h 0 (retainedBefore u as++retainedAfter u as) := by
  simpa only [retainedBefore,retainedAfter,List.append_assoc] using
    (splitMassPartition_mesh u hu as ha u.property.le hm).append_one hh

 def retainedPairSample (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : PositiveMass) (as : List PositiveMass)
    (P : S → S → ℝ) (x : ι → ℝ) : ℝ :=
  sampledPairDisorder w φ q u.val (retainedBefore u as) (retainedAfter u as) P x

 theorem retainedPairSample_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (as bs : List PositiveMass)
    (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hh : 0≤h) (hk : 0≤k) (hmesh : PartitionMesh h 0 as) (kmesh : PartitionMesh k 0 bs)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |retainedPairSample w φ q u as P x-retainedPairSample w φ q u bs P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*(2*(h+k)*clockVariationBound D q) := by
  have h₁ := retainedMasses_ordered u hu as ha
  have h₂ := retainedMasses_ordered u hu bs hb
  exact sampledPairDisorder_mesh_comparison hw φ D hD hφ q hq u.property.le
    _ _ _ _ h₁.1 h₁.2 h₂.1 h₂.2 (retainedBefore_bounds u as) (retainedBefore_bounds u bs)
    (retainedBefore_end u as) (retainedBefore_end u bs)
    (retainedAfter_end u as) (retainedAfter_end u bs)
    (retainedMasses_mesh u hu as ha hh hmesh) (retainedMasses_mesh u hu bs hb hk kmesh) P hK hP x

 theorem retainedPairSample_cauchy {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (P : S → S → ℝ)
    {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    CauchySeq (fun k => retainedPairSample w φ q u (uniformMasses k) P x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let C := ClockTree.errorJetVariation 2 0 0*K*(2*clockVariationBound D q)
  have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹*C) atTop (𝓝 0) := by
    simpa using uniformMasses_mesh_tendsto.mul_const C
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun n hn m hm => ?_⟩
  rw [Real.dist_eq]
  have hb := retainedPairSample_comparison hw φ D hD hφ q hq u hu
    (uniformMasses n) (uniformMasses m) (uniformMasses_ordered n) (uniformMasses_ordered m)
    (by positivity) (by positivity) (uniformMasses_mesh n) (uniformMasses_mesh m) P hK hP x
  apply hb.trans_lt
  have he : ClockTree.errorJetVariation 2 0 0*K*
      (2*(((n+1:ℕ):ℝ)⁻¹+((m+1:ℕ):ℝ)⁻¹)*clockVariationBound D q)=
      ((n+1:ℕ):ℝ)⁻¹*C+((m+1:ℕ):ℝ)⁻¹*C := by dsimp [C]; ring
  rw [he]
  linarith [hN n hn,hN m hm]

 def pathPairDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : PositiveMass) (P : S → S → ℝ) (x : ι → ℝ) : ℝ :=
  limUnder atTop (fun k => retainedPairSample w φ q u (uniformMasses k) P x)

 theorem retainedPairSample_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (u : PositiveMass) (hu : u.val≤1) (P : S → S → ℝ)
    {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    Tendsto (fun k => retainedPairSample w φ q u (uniformMasses k) P x) atTop
      (𝓝 (pathPairDisorder w φ q u P x)) :=
  (retainedPairSample_cauchy hw φ D hD hφ q hq u hu P hK hP x).tendsto_limUnder

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem partitionSample_cross_error {q r : ℝ → ℝ}
    (hq : MonotoneOn q (Icc (0:ℝ) 1)) (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hm : PartitionMesh h 0 as) (hk : PartitionMesh k 0 bs) :
    (∫ u in (0:ℝ)..1, |partitionSample q 0 as u-partitionSample r 0 bs u|) ≤
      h*(q 1-q 0)+k*(r 1-r 0)+(∫ u in (0:ℝ)..1, |q u-r u|) := by
  have hiq : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hir : IntervalIntegrable r volume 0 1 :=
    (show MonotoneOn r (uIcc (0:ℝ) 1) by simpa using hr).intervalIntegrable
  have hia := partitionSample_intervalIntegrable q 0 as 0 1
  have hib := partitionSample_intervalIntegrable r 0 bs 0 1
  calc
    _ ≤ ∫ u in (0:ℝ)..1, (|q u-partitionSample q 0 as u|+
        |r u-partitionSample r 0 bs u|+|q u-r u|) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hia.sub hib).abs
        (((hiq.sub hia).abs.add (hir.sub hib).abs).add (hiq.sub hir).abs)
      intro u hu
      have h₁ := abs_sub_le (partitionSample q 0 as u) (q u) (partitionSample r 0 bs u)
      have h₂ := abs_sub_le (q u) (r u) (partitionSample r 0 bs u)
      rw [abs_sub_comm (partitionSample q 0 as u) (q u)] at h₁
      linarith
    _ = (∫ u in (0:ℝ)..1, |q u-partitionSample q 0 as u|)+
        (∫ u in (0:ℝ)..1, |r u-partitionSample r 0 bs u|)+
        (∫ u in (0:ℝ)..1, |q u-r u|) := by
      rw [intervalIntegral.integral_add
        ((hiq.sub hia).abs.add (hir.sub hib).abs) (hiq.sub hir).abs,
        intervalIntegral.integral_add (hiq.sub hia).abs (hir.sub hib).abs]
    _ ≤ _ := by linarith [partitionSample_l1_error hq as ha hm, partitionSample_l1_error hr bs hb hk]

 def clockL1Distance (D : ι → ℝ) (q r : ℝ → ι → ℝ≥0) : ℝ :=
  (1/2:ℝ)*∑ i, (D i)^2*(∫ u in (0:ℝ)..1, |(q u i:ℝ)-(r u i:ℝ)|)

 theorem sampledDisorderPressure_cross_comparison [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hm : PartitionMesh h 0 as) (hk : PartitionMesh k 0 bs) (x : ι → ℝ) :
    |sampledDisorderPressure w φ C q as x-sampledDisorderPressure w φ C r bs x| ≤
      h*clockVariationBound D q+k*clockVariationBound D r+clockL1Distance D q r := by
  have ht := stepDisorderPressure_l1_comparison hw φ C D hC hD (q 0) (r 0)
    (sampleClockSteps q 0 as) (sampleClockSteps r 0 bs)
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered r bs hb) x
  simp_rw [sampleClockSteps_function q hq as ha,sampleClockSteps_function r hr bs hb] at ht
  apply ht.trans
  calc
    _ ≤ (1/2:ℝ)*∑ i, (D i)^2*(h*((q 1 i:ℝ)-(q 0 i:ℝ))+
        k*((r 1 i:ℝ)-(r 0 i:ℝ))+(∫ u in (0:ℝ)..1, |(q u i:ℝ)-(r u i:ℝ)|)) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply partitionSample_cross_error _ _ as bs ha hb hm hk
      · intro u hu v hv huv
        exact_mod_cast (hq i) hu hv huv
      · intro u hu v hv huv
        exact_mod_cast (hr i) hu hv huv
    _ = _ := by
      unfold clockVariationBound clockL1Distance
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

 theorem pathDisorderPressure_l1_comparison [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q r : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hr : ∀ i, MonotoneOn (fun u => r u i) (Icc (0:ℝ) 1)) (x : ι → ℝ) :
    |pathDisorderPressure w φ C q x-pathDisorderPressure w φ C r x| ≤ clockL1Distance D q r := by
  have ht := ((sampledDisorderPressure_tendsto hw φ C D hC hD q hq x).sub
    (sampledDisorderPressure_tendsto hw φ C D hC hD r hr x)).abs
  have hu : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q+
      ((n+1:ℕ):ℝ)⁻¹*clockVariationBound D r+clockL1Distance D q r)
      atTop (𝓝 (clockL1Distance D q r)) := by
    simpa using ((uniformMasses_mesh_tendsto.mul_const (clockVariationBound D q)).add
      (uniformMasses_mesh_tendsto.mul_const (clockVariationBound D r))).add_const (clockL1Distance D q r)
  exact le_of_tendsto_of_tendsto ht hu (Eventually.of_forall fun n =>
    sampledDisorderPressure_cross_comparison hw φ C D hC hD q r hq hr
      (uniformMasses n) (uniformMasses n) (uniformMasses_ordered n) (uniformMasses_ordered n)
      (uniformMasses_mesh n) (uniformMasses_mesh n) x)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 omit [Fintype ι] in
 theorem stepClockFunction_intervalIntegrable (q₀ : ι → ℝ) {L : List (GaussianStep ι)}
    {a : ℝ} (ho : OrderedSteps a L) (i : ι) (c d : ℝ) :
    IntervalIntegrable (fun u => stepClockFunction q₀ L u i) volume c d := by
  simp_rw [stepClockFunction_eq q₀ ho]
  exact massStepFunction_intervalIntegrable _ _ _ _

 theorem partitionSample_compare_integral {f q : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1) (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as) :
    (∫ u in (0:ℝ)..1, |f u-partitionSample q 0 as u|) ≤
      (∫ u in (0:ℝ)..1, |f u-q u|)+h*(q 1-q 0) := by
  have hiq : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hia := partitionSample_intervalIntegrable q 0 as 0 1
  calc
    _ ≤ ∫ u in (0:ℝ)..1, (|f u-q u|+|q u-partitionSample q 0 as u|) :=
      intervalIntegral.integral_mono_on (by norm_num) (hf.sub hia).abs
        ((hf.sub hiq).abs.add (hiq.sub hia).abs) (fun u _ => abs_sub_le _ _ _)
    _ = (∫ u in (0:ℝ)..1, |f u-q u|)+(∫ u in (0:ℝ)..1, |q u-partitionSample q 0 as u|) :=
      intervalIntegral.integral_add (hf.sub hiq).abs (hiq.sub hia).abs
    _ ≤ _ := by linarith [partitionSample_l1_error hq as ha hm]

 def stepPathClockDistance (D : ι → ℝ) (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι))
    (q : ℝ → ι → ℝ≥0) : ℝ :=
  (1/2:ℝ)*∑ i, (D i)^2*(∫ u in (0:ℝ)..1, |stepClockFunction (fun i => (q₀ i:ℝ)) L u i-(q u i:ℝ)|)

 theorem stepDisorderPressure_path_comparison [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (ho : OrderedSteps 0 L)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (x : ι → ℝ) :
    |stepDisorderPressure w φ C q₀ L x-pathDisorderPressure w φ C q x| ≤
      stepPathClockDistance D q₀ L q := by
  have hb (n : ℕ) : |stepDisorderPressure w φ C q₀ L x-
      sampledDisorderPressure w φ C q (uniformMasses n) x| ≤
      stepPathClockDistance D q₀ L q+((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q := by
    have ht := stepDisorderPressure_l1_comparison hw φ C D hC hD q₀ (q 0) L
      (sampleClockSteps q 0 (uniformMasses n)) ho
      (sampleClockSteps_ordered q _ (uniformMasses_ordered n)) x
    simp_rw [sampleClockSteps_function q hq _ (uniformMasses_ordered n)] at ht
    apply ht.trans
    calc
      _ ≤ (1/2:ℝ)*∑ i, (D i)^2*((∫ u in (0:ℝ)..1,
            |stepClockFunction (fun i => (q₀ i:ℝ)) L u i-(q u i:ℝ)|)+
          ((n+1:ℕ):ℝ)⁻¹*((q 1 i:ℝ)-(q 0 i:ℝ))) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
        intro i _
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply partitionSample_compare_integral
          (stepClockFunction_intervalIntegrable _ ho i 0 1) _ _ (uniformMasses_ordered n) (uniformMasses_mesh n)
        intro u hu v hv huv
        exact_mod_cast (hq i) hu hv huv
      _ = _ := by
        unfold stepPathClockDistance clockVariationBound
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hl := ((tendsto_const_nhds (x := stepDisorderPressure w φ C q₀ L x)).sub
    (sampledDisorderPressure_tendsto hw φ C D hC hD q hq x)).abs
  have hr : Tendsto (fun n : ℕ => stepPathClockDistance D q₀ L q+
      ((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q) atTop (𝓝 (stepPathClockDistance D q₀ L q)) := by
    simpa using tendsto_const_nhds.add (uniformMasses_mesh_tendsto.mul_const (clockVariationBound D q))
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hb)

 theorem stepDisorderPressure_tendsto_path [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q₀ : ℕ → ι → ℝ≥0) (L : ℕ → List (GaussianStep ι)) (ho : ∀ n, OrderedSteps 0 (L n))
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hL : Tendsto (fun n => stepPathClockDistance D (q₀ n) (L n) q) atTop (𝓝 0)) (x : ι → ℝ) :
    Tendsto (fun n => stepDisorderPressure w φ C (q₀ n) (L n) x) atTop
      (𝓝 (pathDisorderPressure w φ C q x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun n =>
    stepDisorderPressure_path_comparison hw φ C D hC hD (q₀ n) (L n) (ho n) q hq x) hL

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι]

 theorem clockCoordinateDistance_integral (D : ι → ℝ) (f g : ℝ → ι → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun u => f u i) volume 0 1)
    (hg : ∀ i, IntervalIntegrable (fun u => g u i) volume 0 1) :
    (∫ u in (0:ℝ)..1, clockCoordinateDistance D (f u) (g u))=
      ∑ i, (∫ u in (0:ℝ)..1, |f u i-g u i|)*(D i)^2 := by
  unfold clockCoordinateDistance
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_mul_const]
  · exact fun i _ => ((hf i).sub (hg i)).abs.mul_const _

 theorem stepClock_sample_distance (D : ι → ℝ) (q₀ : ι → ℝ≥0)
    (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as) :
    (∫ u in (0:ℝ)..1, clockCoordinateDistance D
      (stepClockFunction (fun i => (q₀ i:ℝ)) L u)
      (fun i => partitionSample (fun u => (q u i:ℝ)) 0 as u)) ≤
      2*stepPathClockDistance D q₀ L q+2*h*clockVariationBound D q := by
  rw [clockCoordinateDistance_integral D _ _
    (fun i => stepClockFunction_intervalIntegrable _ hL i 0 1)
    (fun i => partitionSample_intervalIntegrable _ _ _ _ _)]
  calc
    _ ≤ ∑ i, ((∫ u in (0:ℝ)..1, |stepClockFunction (fun i => (q₀ i:ℝ)) L u i-(q u i:ℝ)|)+
        h*((q 1 i:ℝ)-(q 0 i:ℝ)))*(D i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply partitionSample_compare_integral (stepClockFunction_intervalIntegrable _ hL i 0 1)
        _ as ha hm
      intro u hu v hv huv
      exact_mod_cast (hq i) hu hv huv
    _ = _ := by
      unfold stepPathClockDistance clockVariationBound
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

 def stepPathPairDistance (D : ι → ℝ) (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι))
    (q : ℝ → ι → ℝ≥0) (u : ℝ) : ℝ :=
    clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length) (fun i => (q u i:ℝ))+
      2*stepPathClockDistance D q₀ (A++B) q+
    clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
      (fun i => (q 1 i:ℝ))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem stepPairDisorder_sample_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι)) {u : ℝ}
    (hu : 0≤u) (hA : OrderedSteps 0 A) (hB : OrderedSteps u B) (hAu : ∀ s ∈ A, s.1≤u)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered u bs)
    (hau : ∀ a ∈ as, a.val≤u) (heA : partitionEnd 0 as=u) (hetB : partitionEnd u bs=1)
    {h : ℝ} (hmesh : PartitionMesh h 0 (as++bs))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPairDisorder w φ q₀ A B P x-sampledPairDisorder w φ q u as bs P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*
        (stepPathPairDistance D q₀ A B q u+2*h*clockVariationBound D q) := by
  have hoa : MassOrdered 0 (as++bs) := ha.append_end (heA.symm ▸ hb)
  have ht := stepPairDisorder_l1_comparison hw φ D hD hφ q₀ (q 0)
    A B (sampleClockSteps q 0 as) (sampleClockSteps q u bs) hu hA hB
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb)
    hAu (sampleClockSteps_mass_le q 0 as hau) P hK hP x
  rw [sampleClockSteps_terminal q hq 0 as ha,heA] at ht
  have hAB : sampleClockSteps q 0 as++sampleClockSteps q u bs=sampleClockSteps q 0 (as++bs) := by
    rw [sampleClockSteps_append,heA]
  rw [hAB,sampleClockSteps_terminal q hq 0 (as++bs) hoa,
    partitionEnd_append,heA,hetB] at ht
  have hfun : stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as++bs)) =
      fun u i => partitionSample (fun v => (q v i:ℝ)) 0 (as++bs) u := by
    funext u i
    exact sampleClockSteps_function q hq _ hoa u i
  rw [hfun] at ht
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ClockTree.errorJetVariation_nonneg 2 0 0) hK)
  have hh := stepClock_sample_distance D q₀ (A++B) (hA.append_bound hu hAu hB) q hq (as++bs) hoa hmesh
  dsimp only [stepPathPairDistance]
  linarith

 theorem stepPairDisorder_path_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (A B : List (GaussianStep ι)) (u : PositiveMass) (hu : u.val≤1)
    (hA : OrderedSteps 0 A) (hB : OrderedSteps u.val B) (hAu : ∀ s ∈ A, s.1≤u.val)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPairDisorder w φ q₀ A B P x-pathPairDisorder w φ q u P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*stepPathPairDistance D q₀ A B q u.val := by
  have hb (n : ℕ) : |stepPairDisorder w φ q₀ A B P x-
      retainedPairSample w φ q u (uniformMasses n) P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*
        (stepPathPairDistance D q₀ A B q u.val+2*((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q) := by
    have ho := retainedMasses_ordered u hu (uniformMasses n) (uniformMasses_ordered n)
    exact stepPairDisorder_sample_comparison hw φ D hD hφ q₀ A B u.property.le hA hB hAu
      q hq _ _ ho.1 ho.2 (retainedBefore_bounds u _) (retainedBefore_end u _) (retainedAfter_end u _)
      (retainedMasses_mesh u hu _ (uniformMasses_ordered n) (by positivity) (uniformMasses_mesh n)) P hK hP x
  have hl := ((tendsto_const_nhds (x := stepPairDisorder w φ q₀ A B P x)).sub (retainedPairSample_tendsto hw φ D hD hφ q hq u hu P hK hP x)).abs
  have hr : Tendsto (fun n : ℕ => ClockTree.errorJetVariation 2 0 0*K*
      (stepPathPairDistance D q₀ A B q u.val+2*((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q)) atTop
      (𝓝 (ClockTree.errorJetVariation 2 0 0*K*stepPathPairDistance D q₀ A B q u.val)) := by
    simpa using (tendsto_const_nhds.add ((uniformMasses_mesh_tendsto.const_mul 2).mul_const
      (clockVariationBound D q))).const_mul (ClockTree.errorJetVariation 2 0 0*K)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall hb)

 theorem stepPairDisorder_tendsto_path {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ℕ → ι → ℝ≥0) (A B : ℕ → List (GaussianStep ι)) (u : PositiveMass) (hu : u.val≤1)
    (hA : ∀ n, OrderedSteps 0 (A n)) (hB : ∀ n, OrderedSteps u.val (B n))
    (hAu : ∀ n s, s ∈ A n → s.1≤u.val)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (hpath : Tendsto (fun n => stepPathPairDistance D (q₀ n) (A n) (B n) q u.val) atTop (𝓝 0))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    Tendsto (fun n => stepPairDisorder w φ (q₀ n) (A n) (B n) P x) atTop
      (𝓝 (pathPairDisorder w φ q u P x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n =>
    stepPairDisorder_path_comparison hw φ D hD hφ (q₀ n) (A n) (B n) u hu (hA n) (hB n) (hAu n) q hq P hK hP x)
  simpa using hpath.const_mul (ClockTree.errorJetVariation 2 0 0*K)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem partitionSample_comp (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) (u : ℝ) :
    partitionSample q a as u=q (partitionSample id a as u) := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [partitionSample_cons]
    split_ifs <;> simp_all

 theorem partitionSample_id_bounds {h a u : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hm : PartitionMesh h a as) (hu : u ∈ Icc a 1) :
    a ≤ partitionSample id a as u ∧ partitionSample id a as u ≤ u ∧
      u-partitionSample id a as u ≤ h := by
  induction as generalizing a with
  | nil =>
    change 1-a≤h at hm
    simpa only [partitionSample_nil,id_eq] using
      (show a≤a ∧ a≤u ∧ u-a≤h from ⟨le_rfl,hu.1,by linarith [hu.2]⟩)
  | cons b bs ih =>
    rw [partitionSample_cons]
    split_ifs with hb
    · exact ⟨le_rfl,hu.1,by dsimp; linarith [hm.1]⟩
    · obtain ⟨h₁,h₂,h₃⟩ := ih ho.2.2 hm.2 ⟨le_of_not_gt hb,hu.2⟩
      exact ⟨ho.2.1.trans h₁,h₂,h₃⟩

 theorem partitionSample_tendsto {q : ℝ → ℝ} {a u : ℝ}
    (as : ℕ → List PositiveMass) (h : ℕ → ℝ)
    (ho : ∀ n, MassOrdered a (as n)) (hm : ∀ n, PartitionMesh (h n) a (as n))
    (hh : Tendsto h atTop (𝓝 0)) (hu : u ∈ Icc a 1)
    (hc : ContinuousWithinAt q (Icc a 1) u) :
    Tendsto (fun n => partitionSample q a (as n) u) atTop (𝓝 (q u)) := by
  have ht : Tendsto (fun n => partitionSample id a (as n) u) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) _ hh
    intro n
    have hb := partitionSample_id_bounds (as n) (ho n) (hm n) hu
    rw [abs_of_nonpos (sub_nonpos.mpr hb.2.1)]
    linarith [hb.2.2]
  have hw : Tendsto (fun n => partitionSample id a (as n) u) atTop (𝓝[Icc a 1] u) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht,Eventually.of_forall fun n =>
      let hb := partitionSample_id_bounds (as n) (ho n) (hm n) hu
      ⟨hb.1,hb.2.1.trans hu.2⟩⟩
  have he : (fun n => partitionSample q a (as n) u) =
      (fun n => q (partitionSample id a (as n) u)) := funext (fun n => partitionSample_comp q a (as n) u)
  rw [he]
  exact hc.tendsto.comp hw

 theorem uniformSample_tendsto {q : ℝ → ℝ} {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hc : ContinuousWithinAt q (Icc (0:ℝ) 1) u) :
    Tendsto (fun n => partitionSample q 0 (uniformMasses n) u) atTop (𝓝 (q u)) :=
  partitionSample_tendsto _ _ uniformMasses_ordered uniformMasses_mesh
    uniformMasses_mesh_tendsto hu hc

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def pathPairMoment (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (P : S → S → ℝ) (u : ℝ) : ℝ :=
  if h : 0<u then pathPairDisorder w φ q ⟨u,h⟩ P 0 else 0

 theorem stepPairMoment_path_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) :
    |stepPairMoment w φ q₀ L hL.mem_pos P u-pathPairMoment w φ q P u| ≤
      ClockTree.errorJetVariation 2 0 0*K*(
        clockCoordinateDistance D (stepClockFunction (fun i => (q₀ i:ℝ)) L u)
          (fun i => (q u i:ℝ))+2*stepPathClockDistance D q₀ L q+
        clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) L L.length)
          (fun i => (q 1 i:ℝ))) := by
  have ho := splitClockSteps_ordered u ⟨hu.1.le,hu.2⟩ L hL hu.1.le
  rw [stepPairMoment_eq_split hw φ q₀ L hL, pathPairMoment,dite_eq_left hu.1]
  have hb := stepPairDisorder_path_comparison hw φ D hD hφ q₀
    (splitClockSteps u L).1 (splitClockSteps u L).2 ⟨u,hu.1⟩ hu.2
    ho.1 ho.2.1 ho.2.2 q hq P hK hP 0
  simpa only [stepPathPairDistance,splitClockSteps_append,←stepClockFunction_split _ _ _ hL] using hb

 omit [Nonempty ι] in
 theorem sample_stepPathClockDistance_le (D : ι → ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as) :
    stepPathClockDistance D (q 0) (sampleClockSteps q 0 as) q≤h*clockVariationBound D q := by
  unfold stepPathClockDistance clockVariationBound
  simp_rw [sampleClockSteps_function q hq as ha]
  calc
    _ ≤ (1/2:ℝ)*∑ i, (D i)^2*(h*((q 1 i:ℝ)-(q 0 i:ℝ))) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      simp_rw [abs_sub_comm (partitionSample _ _ _ _)]
      exact partitionSample_l1_error (fun u hu v hv huv => by exact_mod_cast hq i hu hv huv) as ha hm
    _ = _ := by simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

 omit [Nonempty ι] in
 theorem stepPathClockDistance_nonneg (D : ι → ℝ) (q₀ : ι → ℝ≥0)
    (L : List (GaussianStep ι)) (q : ℝ → ι → ℝ≥0) :
    0 ≤ stepPathClockDistance D q₀ L q := by
  unfold stepPathClockDistance
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (sq_nonneg _) (intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _))))

 theorem uniformMassTail_end {h : ℝ} (hh : 0<h) (k n : ℕ) :
    partitionEnd ((k:ℝ)*h) (uniformMassTail h hh k n)=(k+n:ℕ)*h := by
  induction n generalizing k with
  | zero => simp [uniformMassTail,partitionEnd]
  | succ n ih =>
    simp only [uniformMassTail,partitionEnd]
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (k+1)

 theorem uniformMasses_end (n : ℕ) : partitionEnd 0 (uniformMasses n)=1 := by
  have he := uniformMassTail_end (show 0<((n+1:ℕ):ℝ)⁻¹ by positivity) 0 (n+1)
  simpa [uniformMasses, mul_inv_cancel₀ (show ((n:ℝ)+1)≠0 by positivity)] using he

 theorem sampledPairMoment_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1)
    (hc : ∀ i, ContinuousWithinAt (fun v => (q v i:ℝ)) (Icc (0:ℝ) 1) u) :
    Tendsto (fun n => stepPairMoment w φ (q 0) (sampleClockSteps q 0 (uniformMasses n))
      (sampleClockSteps_ordered q _ (uniformMasses_ordered n)).mem_pos P u)
      atTop (𝓝 (pathPairMoment w φ q P u)) := by
  have ht : Tendsto (fun n => clockCoordinateDistance D
      (stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (uniformMasses n)) u)
      (fun i => (q u i:ℝ))) atTop (𝓝 0) := by
    unfold clockCoordinateDistance
    simp_rw [sampleClockSteps_function q hq _ (uniformMasses_ordered _)]
    have hh := tendsto_finsetSum Finset.univ (fun i _ =>
      ((uniformSample_tendsto ⟨hu.1.le,hu.2⟩ (hc i)).sub_const (q u i:ℝ)).abs.mul_const ((D i)^2))
    simpa using hh
  have hl : Tendsto (fun n => stepPathClockDistance D (q 0)
      (sampleClockSteps q 0 (uniformMasses n)) q) atTop (𝓝 0) :=
    squeeze_zero (fun _ => stepPathClockDistance_nonneg _ _ _ _) (fun n =>
      sample_stepPathClockDistance_le D q hq _ (uniformMasses_ordered n) (uniformMasses_mesh n))
      (by simpa using uniformMasses_mesh_tendsto.mul_const (clockVariationBound D q))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => stepPairMoment_path_comparison hw φ D hD hφ
    (q 0) _ (sampleClockSteps_ordered q _ (uniformMasses_ordered n)) q hq P hK hP hu)
  simp_rw [sampleClockSteps_terminal q hq _ _ (uniformMasses_ordered _),uniformMasses_end]
  simpa [clockCoordinateDistance] using (ht.add (hl.const_mul 2)).const_mul (ClockTree.errorJetVariation 2 0 0*K)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 omit [Nonempty ι] in
 theorem ClockTree.disorderExpect_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : T.Assignment → ℝ) {K : ℝ} (hP : ∀ σ, |P σ|≤K) (x : ι → ℝ) :
    |T.disorderExpect w φ v q P x|≤K := by
  rw [T.disorderExpect_integral hw φ ha]
  have hb (y : ι → ℝ) : |T.expect w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) P (x+y)|≤K := by
    rw [T.expect_realize]
    exact (T.realize _).expect_abs_le hw φ (clockSteps_ordered ha _) (fun σ => hP _) _
  have hi := norm_integral_le_of_norm_le_const (f := fun y =>
    T.expect w φ (cumulativeIncrements (q 0) (fun j => q (j+1))) P (x+y))
    (μ := Measure.pi fun i => gaussianReal 0 (q 0 i-v i).toNNReal)
    (Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb y))
  simpa only [zeroContinuation,Real.norm_eq_abs,probReal_univ,mul_one] using hi

 omit [Nonempty ι] in
 theorem cumulativePair_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q : ℕ → ι → ℝ) (j : ℕ) (P : S → S → ℝ) {K : ℝ} (hP : ∀ σ τ, |P σ τ|≤K) :
    |cumulativePair w φ as q j P|≤K :=
  ClockTree.disorderExpect_bound hw φ _ ha _ _ _ (fun _ => hP _ _) _

 theorem stepPairMoment_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L) (P : S → S → ℝ)
    {K : ℝ} (hP : ∀ σ τ, |P σ τ|≤K) (u : ℝ) :
    |stepPairMoment w φ q₀ L hL.mem_pos P u|≤K := by
  unfold stepPairMoment
  rw [massStepFunction_split_index]
  exact cumulativePair_bound hw φ _ (positiveStepMasses_ordered hL _) _ _ P hP

 omit [Nonempty ι] in
 theorem stepPairDisorder_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (A B : List (GaussianStep ι)) (ho : OrderedSteps 0 (A++B)) (P : S → S → ℝ)
    {K : ℝ} (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPairDisorder w φ q₀ A B P x|≤K := by
  have hA : ∀ s ∈ A, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_left _ hs)
  have hB : ∀ s ∈ B, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_right _ hs)
  have hc := congr_fun (ClockTree.pairDisorder_coordinates hw φ A B hA hB ho q₀ P) x
  rw [←hc]
  apply ClockTree.disorderExpect_bound hw φ
  · rw [←positiveStepMasses_append]
    exact positiveStepMasses_ordered ho _
  · exact fun σ => hP _ _

 theorem pathPairMoment_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K)
    {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1) : |pathPairMoment w φ q P u|≤K := by
  rw [pathPairMoment,dite_eq_left hu.1]
  apply le_of_tendsto ((retainedPairSample_tendsto hw φ D hD hφ q hq ⟨u,hu.1⟩ hu.2 P hK hP 0).abs)
  apply Eventually.of_forall
  intro n
  change |stepPairDisorder w φ (q 0)
    (sampleClockSteps q 0 (retainedBefore ⟨u,hu.1⟩ (uniformMasses n)))
    (sampleClockSteps q u (retainedAfter ⟨u,hu.1⟩ (uniformMasses n))) P 0|≤K
  have ho := retainedMasses_ordered (⟨u,hu.1⟩ : PositiveMass) hu.2 (uniformMasses n) (uniformMasses_ordered n)
  apply stepPairDisorder_bound hw φ _ _ _ _ P hP
  exact (sampleClockSteps_ordered q _ ho.1).append_bound hu.1.le
    (sampleClockSteps_mass_le q _ _ (retainedBefore_bounds ⟨u,hu.1⟩ _))
    (sampleClockSteps_ordered q _ ho.2)

end SKFluctuations.Hierarchy

end

end OAI
