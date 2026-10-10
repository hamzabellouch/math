import Mathlib
import OAI.Probability.SKFluctuations.ComparisonCapTravel
import OAI.Probability.SKFluctuations.InverseConstraintNonempty

namespace OAI

/-! Clock Retain Two. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

 theorem MassOrdered.le_of_mem {a : ℝ} {as : List PositiveMass}
    (ha : MassOrdered a as) {b : PositiveMass} (hb : b ∈ as) : a≤b.val := by
  induction as generalizing a with
  | nil => simp at hb
  | cons c cs ih =>
    rcases List.mem_cons.mp hb with rfl|hb
    · exact ha.2.1
    · exact ha.2.1.trans (ih ha.2.2 hb)

 theorem partitionSample_at_start (q : ℝ → ℝ) {a : ℝ} (as : List PositiveMass)
    (ha : MassOrdered a as) : partitionSample q a as a=q a := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rw [partitionSample_cons]
    split_ifs with hab
    · rfl
    · have he : a=b.val := le_antisymm ha.2.1 (le_of_not_gt hab)
      subst a
      exact ih ha.2.2

 theorem partitionSample_at_node (q : ℝ → ℝ) {a : ℝ} (as : List PositiveMass)
    (ha : MassOrdered a as) {u : PositiveMass} (hu : u ∈ as) :
    partitionSample q a as u.val=q u.val := by
  induction as generalizing a with
  | nil => simp at hu
  | cons b bs ih =>
    rcases List.mem_cons.mp hu with rfl|hu
    · rw [partitionSample_cons,ite_eq_right (lt_irrefl _)]
      exact partitionSample_at_start q _ ha.2.2
    · rw [partitionSample_cons,ite_eq_right (not_lt.mpr (ha.2.2.le_of_mem hu))]
      exact ih ha.2.2 hu

 def insertMass (u : PositiveMass) (as : List PositiveMass) : List PositiveMass :=
   (splitMassPartition u as).1++(splitMassPartition u as).2

 theorem insertMass_ordered (u : PositiveMass) (hu : u.val≤1)
    (as : List PositiveMass) (ha : MassOrdered 0 as) : MassOrdered 0 (insertMass u as) := by
  obtain ⟨h₁,h₂⟩ := splitMassPartition_ordered u hu as ha u.property.le
  apply h₁.append_end
  simpa only [splitMassPartition_end] using h₂

 theorem mem_insertMass_self (u : PositiveMass) (as : List PositiveMass) : u ∈ insertMass u as := by
  induction as with
  | nil => simp [insertMass,splitMassPartition]
  | cons b bs ih =>
    unfold insertMass splitMassPartition
    split_ifs
    · exact List.mem_cons_of_mem _ ih
    · simp

 theorem mem_insertMass_of_mem (u : PositiveMass) {as : List PositiveMass}
    {v : PositiveMass} (hv : v ∈ as) : v ∈ insertMass u as := by
  induction as with
  | nil => simp at hv
  | cons b bs ih =>
    unfold insertMass splitMassPartition
    split_ifs
    · rcases List.mem_cons.mp hv with rfl|hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hv)
    · exact List.mem_cons_of_mem _ hv

 theorem insertMass_end (u : PositiveMass) (as : List PositiveMass)
    (hu : u.val≤1) (he : partitionEnd 0 as=1) : partitionEnd 0 (insertMass u as)=1 := by
  have hgen : ∀ {a : ℝ} (bs : List PositiveMass), a≤u.val → u.val≤partitionEnd a bs →
      partitionEnd a (insertMass u bs)=partitionEnd a bs := by
    intro a bs
    induction bs generalizing a with
    | nil =>
      intro hau hua
      exact le_antisymm hua hau
    | cons b bs ih =>
      intro hau hue
      unfold insertMass splitMassPartition
      split_ifs with hbu
      · exact ih hbu.le hue
      · rfl
  exact (hgen as u.property.le (he ▸ hu)).trans he

 def twoCutMasses (u v : PositiveMass) (n : ℕ) : List PositiveMass :=
   insertMass u (insertMass v (uniformMasses n))

 theorem twoCutMasses_ordered (u v : PositiveMass) (hu : u.val≤1) (hv : v.val≤1) (n : ℕ) :
    MassOrdered 0 (twoCutMasses u v n) :=
  insertMass_ordered u hu _ (insertMass_ordered v hv _ (uniformMasses_ordered n))

 theorem twoCutMasses_mesh (u v : PositiveMass) (hu : u.val≤1) (hv : v.val≤1) (n : ℕ) :
    PartitionMesh (((n+1:ℕ):ℝ)⁻¹) 0 (twoCutMasses u v n) :=
  splitMassPartition_mesh u hu _ (insertMass_ordered v hv _ (uniformMasses_ordered n)) u.property.le
    (splitMassPartition_mesh v hv _ (uniformMasses_ordered n) v.property.le (uniformMasses_mesh n))

 theorem twoCutMasses_nodes (u v : PositiveMass) (n : ℕ) :
    u ∈ twoCutMasses u v n ∧ v ∈ twoCutMasses u v n :=
  ⟨mem_insertMass_self u _,mem_insertMass_of_mem u (mem_insertMass_self v _)⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 theorem retainedMoment_tendsto {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (h : ℕ → ℝ)
    (ho : ∀ n, MassOrdered 0 (as n)) (hm : ∀ n, PartitionMesh (h n) 0 (as n))
    (he : ∀ n, partitionEnd 0 (as n)=1) (hh : Tendsto h atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ n, u ∈ as n)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    Tendsto (fun n => stepPairMoment w φ (q 0) (sampleClockSteps q 0 (as n))
      (sampleClockSteps_ordered q _ (ho n)).mem_pos P u.val)
      atTop (𝓝 (pathPairMoment w φ q P u.val)) := by
  have ht (n : ℕ) : clockCoordinateDistance D
      (stepClockFunction (fun i => (q 0 i:ℝ)) (sampleClockSteps q 0 (as n)) u.val)
      (fun i => (q u.val i:ℝ))=0 := by
    unfold clockCoordinateDistance
    simp_rw [sampleClockSteps_function q hq _ (ho n),partitionSample_at_node _ _ (ho n) (hnode n)]
    simp
  have hl : Tendsto (fun n => stepPathClockDistance D (q 0)
      (sampleClockSteps q 0 (as n)) q) atTop (𝓝 0) :=
    squeeze_zero (fun _ => stepPathClockDistance_nonneg _ _ _ _) (fun n =>
      sample_stepPathClockDistance_le D q hq _ (ho n) (hm n))
      (by simpa using hh.mul_const (clockVariationBound D q))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun n => stepPairMoment_path_comparison hw φ D hD hφ
    (q 0) _ (sampleClockSteps_ordered q _ (ho n)) q hq P hK hP ⟨u.property,hu⟩)
  simp_rw [ht,sampleClockSteps_terminal q hq _ _ (ho _),he]
  simpa [clockCoordinateDistance] using (hl.const_mul 2).const_mul (ClockTree.errorJetVariation 2 0 0*K)

 theorem retainedMoment_tendsto_all {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (h : ℕ → ℝ)
    (ho : ∀ n, MassOrdered 0 (as n)) (hm : ∀ n, PartitionMesh (h n) 0 (as n))
    (he : ∀ n, partitionEnd 0 (as n)=1) (hh : Tendsto h atTop (𝓝 0))
    (u : PositiveMass) (hu : u.val≤1) (hnode : ∀ n, u ∈ as n) (P : S → S → ℝ) :
    Tendsto (fun n => stepPairMoment w φ (q 0) (sampleClockSteps q 0 (as n))
      (sampleClockSteps_ordered q _ (ho n)).mem_pos P u.val)
      atTop (𝓝 (pathPairMoment w φ q P u.val)) := by
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
  exact retainedMoment_tendsto hw φ D hD hφ q hq as h ho hm he hh u hu hnode P hK hP

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

 theorem rootLevelPairMean_product_monotone {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (A : S → ℝ)
    (steps : List (GaussianStep ι)) {a : ℝ} (ha : OrderedSteps a steps) :
    Monotone (fun j => rootLevelPairMean w φ q (fun σ τ => A σ*A τ) steps j) := by
  intro j k hjk
  apply integral_mono
    ((levelPairMean_smooth hw φ _ steps ha j 0).integrable_zero_shift 0)
    ((levelPairMean_smooth hw φ _ steps ha k 0).integrable_zero_shift 0)
  intro x
  exact levelPairMean_product_monotone hw φ A steps ha (0+x) hjk

 theorem cumulativePair_product_monotone {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass)
    (ha : MassOrdered 0 as) (q : ℕ → ι → ℝ) (A : S → ℝ) :
    Monotone (fun j => cumulativePair w φ as q j (fun σ τ => A σ*A τ)) := by
  have he (j : ℕ) : cumulativePair w φ as q j (fun σ τ => A σ*A τ)=
      rootLevelPairMean w φ (fun i => (q 0 i).toNNReal) (fun σ τ => A σ*A τ)
        (diagonalBoundarySteps as (q 0) (fun k => q (k+1))) j :=
    ClockTree.pairDisorder_eq_rootLevelPairMean hw φ as ha q j (fun σ τ => A σ*A τ)
  simp_rw [he]
  apply rootLevelPairMean_product_monotone hw φ
  rw [←clockSteps_cumulative]
  exact clockSteps_ordered ha _

omit [Fintype ι] in
 theorem splitClockSteps_length_monotone [Fintype ι] (L : List (GaussianStep ι)) :
    Monotone (fun u : ℝ => (splitClockSteps u L).1.length) := by
  intro u v huv
  induction L with
  | nil => exact le_rfl
  | cons s L ih =>
    simp only [splitClockSteps]
    split_ifs with hsu hsv hsv
    · simpa only [List.length_cons] using Nat.succ_le_succ ih
    · exact False.elim (hsv (hsu.trans huv))
    · exact Nat.zero_le _
    · exact le_rfl

 theorem stepPairMoment_product_monotone [Nonempty ι] {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (L : List (GaussianStep ι)) (ho : OrderedSteps 0 L) (A : S → ℝ) :
    Monotone (stepPairMoment w φ q₀ L ho.mem_pos (fun σ τ => A σ*A τ)) := by
  intro u v huv
  unfold stepPairMoment
  rw [massStepFunction_split_index,massStepFunction_split_index]
  exact cumulativePair_product_monotone hw φ _ (positiveStepMasses_ordered ho _) _ A
    (splitClockSteps_length_monotone L huv)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem pathPairMoment_product_monotone {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (A : S → ℝ) : MonotoneOn (pathPairMoment w φ q (fun σ τ => A σ*A τ)) (Ioc (0:ℝ) 1) := by
  intro u hu v hv huv
  let u' : PositiveMass := ⟨u,hu.1⟩
  let v' : PositiveMass := ⟨v,hv.1⟩
  let as := twoCutMasses u' v'
  have ho (n : ℕ) : MassOrdered 0 (as n) := twoCutMasses_ordered u' v' hu.2 hv.2 n
  have hm (n : ℕ) : PartitionMesh (((n+1:ℕ):ℝ)⁻¹) 0 (as n) :=
    twoCutMasses_mesh u' v' hu.2 hv.2 n
  have he (n : ℕ) : partitionEnd 0 (as n)=1 :=
    insertMass_end u' _ hu.2 (insertMass_end v' _ hv.2 (uniformMasses_end n))
  have h₁ := retainedMoment_tendsto_all hw φ q hq as _ ho hm he uniformMasses_mesh_tendsto
    u' hu.2 (fun n => (twoCutMasses_nodes u' v' n).1) (fun σ τ => A σ*A τ)
  have h₂ := retainedMoment_tendsto_all hw φ q hq as _ ho hm he uniformMasses_mesh_tendsto
    v' hv.2 (fun n => (twoCutMasses_nodes u' v' n).2) (fun σ τ => A σ*A τ)
  exact le_of_tendsto_of_tendsto h₁ h₂ (Filter.Eventually.of_forall fun n =>
    stepPairMoment_product_monotone hw φ (q 0) _ (sampleClockSteps_ordered q _ (ho n)) A huv)

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open Hierarchy MeasureTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*} [Fintype ι] [Nonempty ι]

 theorem pathPairMoment_overlap_monotone (n : ℕ) {w : Spin n → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1)) :
    MonotoneOn (pathPairMoment w φ q (orderedOverlap n)) (Ioc (0:ℝ) 1) := by
  have he : orderedOverlap n = fun σ τ => (1/(n:ℝ))*∑ i, spinValue (σ i)*spinValue (τ i) := by
    funext σ τ
    unfold orderedOverlap
    ring
  intro u hu v hv huv
  rw [he,pathPairMoment_const_mul hw φ q hq _ _ hu,
    pathPairMoment_const_mul hw φ q hq _ _ hv,
    pathPairMoment_finsetSum hw φ q hq _ _ hu,pathPairMoment_finsetSum hw φ q hq _ _ hv]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    pathPairMoment_product_monotone hw φ q hq (fun σ => spinValue (σ i)) hu hv huv) (by positivity)

 theorem pathPairMoment_overlap_sq_monotone (n : ℕ) {w : Spin n → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : Spin n → (ι → ℝ) →L[ℝ] ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1)) :
    MonotoneOn (pathPairMoment w φ q (fun σ τ => (orderedOverlap n σ τ)^2)) (Ioc (0:ℝ) 1) := by
  have he : (fun σ τ => (orderedOverlap n σ τ)^2) =
      fun σ τ => (1/(n:ℝ)^2)*∑ i, ∑ j,
        (spinValue (σ i)*spinValue (σ j))*(spinValue (τ i)*spinValue (τ j)) := by
    funext σ τ
    unfold orderedOverlap
    rw [div_pow,pow_two,Finset.sum_mul_sum,one_div_mul_eq_div]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  intro u hu v hv huv
  rw [he,pathPairMoment_const_mul hw φ q hq _ _ hu,
    pathPairMoment_const_mul hw φ q hq _ _ hv,
    pathPairMoment_finsetSum hw φ q hq _ _ hu,pathPairMoment_finsetSum hw φ q hq _ _ hv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  rw [pathPairMoment_finsetSum hw φ q hq _ _ hu,pathPairMoment_finsetSum hw φ q hq _ _ hv]
  exact Finset.sum_le_sum fun j _ => pathPairMoment_product_monotone hw φ q hq
    (fun σ => spinValue (σ i)*spinValue (σ j)) hu hv huv

 theorem orderedPath_SK_monotone (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    MonotoneOn (orderedPathS n b h) (Ioc (0:ℝ) 1) ∧
      MonotoneOn (orderedPathB n b h) (Ioc (0:ℝ) 1) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact ⟨pathPairMoment_overlap_monotone n (uniformWeight_pos n) (orderedFeature n)
      (orderedPathClock n b h) (orderedPathClock_monotone n hb hh),
    pathPairMoment_overlap_sq_monotone n (uniformWeight_pos n) (orderedFeature n)
      (orderedPathClock n b h) (orderedPathClock_monotone n hb hh)⟩

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

 theorem comparison_minimum_future_center {N δ U L E d r₀ u₀ : ℝ}
    (hN : 0<N) (hU : 0<U) (hL : 0<L) (hLU : L≤U) (hE : 0<E) (hd : 0≤d)
    (hq : 2≤N^δ) (hr₀ : r₀ ∈ Icc (0:ℝ) (1/4)) (hu₀ : u₀ ∈ Icc (0:ℝ) (1/4))
    (n : ℕ) (hn : 0<n) (g : ℝ → ℝ) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let _M' := comparisonCapSlope N δ U L E d
    let c := k 1
    let hr : r₀ ≤ 1 := le_trans hr₀.2 (by norm_num)
    let hu : u₀ ∈ Icc (0:ℝ) 1 := ⟨hu₀.1,le_trans hu₀.2 (by norm_num)⟩
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
    let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
    ∀ (α : inverseIntegralConstraints r₀ u₀ k M)
    (hg : ContDiff ℝ 1 g)
    (_hgpos : ∀ r ∈ Icc r₀ 1, 0<g r)
    (_hp : ∀ r ∈ Ioc r₀ 1, comparisonLogSlope g r ∈ Icc (0:ℝ) 1)
    (b h : ℝ → ℝ)
    (_hb : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => b u-omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) u) (Icc (0:ℝ) 1))
    (_hh : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      MonotoneOn (fun u => h u+omittedExtension hu.2
        (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
          (hg.continuous.mul continuous_id) β) u) (Icc (0:ℝ) 1))
    (_hbn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ b 0-omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous β) 0)
    (_hhn : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      0 ≤ h 0+omittedExtension hu.2 (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) β) 0)
    (_hmin : ∀ β : inverseIntegralConstraints r₀ u₀ k M,
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 α ≤
      inverseCompensatedPressure hr hu.2 hc hk hkc hm hM g hg.continuous n b h 0 β),
    let b' := fun u => (b u-omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
    let h' := fun u => (h u+omittedExtension hu.2
      (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
        (hg.continuous.mul continuous_id) α) u).toNNReal
    ∀ r ∈ Ioc r₀ 1, ∀ s ∈ Icc r 1,
      N^(-δ)*U < α.val.val s-α.val.val r →
      orderedPathS n b' h' (α.val.val r)≤
        s+(L/N^δ)*Real.log ((1+U)/U) := by
  dsimp only
  intro α hg hgpos hp b h hb hh hbn hhn hmin
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  let c := k 1
  let hr : r₀≤1 := le_trans hr₀.2 (by norm_num)
  let hu : u₀≤1 := le_trans hu₀.2 (by norm_num)
  let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
  let hk := comparisonFloor_continuousOn (δ:=δ) hN hU hr₀.1
  let hkc := fun r (hri : r ∈ Icc r₀ 1) => comparisonFloor_lower_on (δ:=δ) hN hU hr₀.1 hri
  let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd
  let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd (show (0:ℝ)≤1 by norm_num)
  let b' := fun u => (b u-omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM g hg.continuous α) u).toNNReal
  let h' := fun u => (h u+omittedExtension hu
    (constrainedCoefficient hr hc hk hkc hm hM (fun r => g r*r)
      (hg.continuous.mul continuous_id) α) u).toNNReal
  let S := fun r => orderedPathS n b' h' (α.val.val r)
  let B := fun r => orderedPathB n b' h' (α.val.val r)
  let J := inverseControlFactor r₀ (fun r => inverseControlWeight α.val.val k M r*
    comparisonCapSlope N δ U L E d (α.val.val r))
  obtain ⟨H,hH,hD,hbang,hzero⟩ := comparison_minimum_contact_potential hN hU hL hLU hE hd
    hq hr₀ hu₀ n hn g α hg (fun r hr => hgpos r ⟨hr.1.le,hr.2⟩) hp b h hb hh hbn hhn hmin
  have hα := inverseConstraint_strictMonoOn hc hk hkc α.property
  have hαL := inverseIntegralConstraints_lipschitz hm hM α.property
  have hαr (r : ℝ) (hri : r ∈ Ioc r₀ 1) : α.val.val r ∈ Ioc (0:ℝ) 1 := by
    refine ⟨?_,(α.val.property.1 r).2⟩
    have ht := hα ⟨le_rfl,hr⟩ ⟨hri.1.le,hri.2⟩ hri.1
    rw [α.property.1] at ht
    exact hu₀.1.trans_lt ht
  have hb' : MonotoneOn b' (Icc (0:ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono ((hb α) hu hv huv)
  have hh' : MonotoneOn h' (Icc (0:ℝ) 1) :=
    fun u hu v hv huv => Real.toNNReal_mono ((hh α) hu hv huv)
  have hSm : MonotoneOn S (Ioc r₀ 1) := by
    intro r hr s hs hrs
    exact (orderedPath_SK_monotone n hn b' h' hb' hh').1 (hαr r hr) (hαr s hs)
      (α.val.property.2 hrs)
  have hbounds (r : ℝ) (hr : r ∈ Ioc r₀ 1) := orderedPath_SK_bounds n hn b' h' hb' hh' (hαr r hr)
  have hD' : ∀ᵐ r, r ∈ Icc r₀ 1 → HasDerivAt H
      ((J r*g r)*comparisonBracket (comparisonLogSlope g r) r (S r) (B r)) r := by
    filter_upwards [hD,volume.ae_ne r₀] with r hDr hrne hri
    have hrpos : 0<r := hr₀.1.trans_lt (lt_of_le_of_ne hri.1 hrne.symm)
    have ht := hDr hri
    change HasDerivAt H (J r*radiusComparisonGradient g α.val.val
      (orderedPathS n b' h') (orderedPathB n b' h') r) r at ht
    rw [comparison_gradient_slope hrpos.ne' (hgpos r hri).ne'] at ht
    exact ht.congr_deriv (by dsimp only [S,B,comparisonBracket]; ring)
  intro r hr s hs hinc
  have hf := potential_future_center_bound hr₀.1 hr hs.1 hs.2 hH
    (fun t ht => mul_pos (inverseControlFactor_pos _ _ _) (hgpos t ht)) hD'
    (hbang.mono fun t ht hti => (ht hti).1)
    (hbang.mono fun t ht hti => (ht hti).2)
    (hzero.mono fun t ht hti hh => (ht hti hh).2.1)
    (fun t ht => (hp t ht).1) hSm (fun t ht => (hbounds t ht).2.1)
    (fun t ht => (hbounds t ht).2.2.1) hαL hα (fun t _ => α.val.property.1 t)
    (comparisonCap_continuous N δ U L E d).continuousOn
    (fun u hu => (comparisonCap_first_term hN hU hL hE hd hu.1).1)
    (comparisonFloor_continuousOn (δ:=δ) hN hU (show (0:ℝ)≤0 by rfl)).integrableOn_Icc
    (fun t ht => (comparisonFloor_pos (δ:=δ) hN hU ht.1).le)
    ((comparisonFloor_total_mass hN hU).trans_lt hinc)
  have hcT := comparisonCap_log_travel (δ:=δ) hN hU hL hE hd (show (0:ℝ)≤0 by rfl)
    (show (0:ℝ)≤1 by norm_num)
  simp only [zero_add] at hcT
  exact hf.trans (by linarith)

end SKFluctuations

 

 

namespace SKFluctuations
open Set

 theorem finite_dyadic_future_cover {x B μ : ℝ} (hx : 0 < x) (hB : 0 < B)
    (hμ : 0 < μ) (hμB : 3*B*μ ≤ 1) :
    ∃ vs : Finset ℝ, (∀ v ∈ vs, 0 < v ∧ 3*B*v ≤ 1) ∧
      ∀ y : ℝ, x ≤ y → μ ≤ y ∨ ∃ v ∈ vs, v ≤ y ∧ y < 2*v := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (μ/x))
  rw [max_eq_right (div_pos hμ hx).le] at hN
  classical
  let vs := ((Finset.range N).image (fun j : ℕ => (2:ℝ)^j*x)).filter (fun v => 3*B*v ≤ 1)
  refine ⟨vs,?_,?_⟩
  · intro v hv
    obtain ⟨hj,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hj
    exact ⟨by positivity,hv⟩
  · intro y hxy
    by_cases hmy : μ ≤ y
    · exact Or.inl hmy
    · right
      have hym : y < μ := lt_of_not_ge hmy
      have hrat : 1 ≤ y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
      obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near hrat (show (1:ℝ) < 2 by norm_num)
      have hvy : (2:ℝ)^j*x ≤ y := (le_div_iff₀ hx).mp hlo
      have hyv : y < 2*((2:ℝ)^j*x) := by
        have hh := (div_lt_iff₀ hx).mp hhi
        rw [pow_succ] at hh
        nlinarith
      have hjpow : (j:ℝ) < (2:ℝ)^j := by exact_mod_cast (Nat.lt_two_pow_self (n := j))
      have hjN : j < N := by
        have hyx : y/x < μ/x := div_lt_div_of_pos_right hym hx
        have hh : (j:ℝ) < N := lt_trans (hjpow.trans_le hlo) (hyx.trans hN)
        exact_mod_cast hh
      refine ⟨(2:ℝ)^j*x,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hjN,rfl⟩,?_⟩,hvy,hyv⟩
      exact (mul_le_mul_of_nonneg_left (hvy.trans hym.le) (by positivity : 0 ≤ 3*B)).trans hμB

 theorem future_window_radius_geometry {α : ℝ → ℝ} {x y v B cl cu R a b A : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hvy : v ≤ y) (hyv : y < 2*v)
    (hcl : 0 < cl) (hcu : 0 < cu) (hB : 2 ≤ B) (hA : 1 ≤ A)
    (hBA : 2*cu*A ≤ B) (hyR : B*y ≤ cl*R)
    (ha : α a=B*v) (hb : α b=2*B*v)
    (hregA : cl*a ≤ α a ∧ α a ≤ cu*a)
    (hregB : cl*b ≤ α b ∧ α b ≤ cu*b) :
    0 < v ∧ A*x ≤ a ∧ a ≤ R ∧ b ≤ (2*cu/cl)*a ∧
      cl*a ≤ B*v ∧ B*v ≤ cu*a ∧ y-x < B*v := by
  have hv : 0 < v := by linarith
  have hB0 : 0 < B := by linarith
  have hAx : 0 < A*x := mul_pos (by linarith) hx
  have hAv : A*x < 2*A*v := by nlinarith
  have hBv : 2*cu*A*v ≤ B*v := mul_le_mul_of_nonneg_right hBA hv.le
  rw [ha] at hregA
  rw [hb] at hregB
  have hAa : A*x ≤ a := by nlinarith
  refine ⟨hv,hAa,?_,?_,hregA.1,hregA.2,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hvy hB0.le
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hcl).mpr
    have hh := mul_le_mul_of_nonneg_left hregA.2 (show (0:ℝ) ≤ 2 by norm_num)
    nlinarith [hregB.1]
  · nlinarith

end SKFluctuations

 

 

namespace SKFluctuations
open Set Hierarchy

 theorem radius_in_regular_region {α : ℝ → ℝ} {r₀ z a p cl cu : ℝ}
    (hα : Monotone α) (ha : a ∈ Icc r₀ 1) (hz : z ∈ Icc r₀ 1)
    (heq : α a=p) (hp : cu*z<p)
    (hreg : ∀ t ∈ Icc z 1, cl*t≤α t ∧ α t≤cu*t) :
    z<a ∧ cl*a≤p ∧ p≤cu*a := by
  have hza : z<a := by
    by_contra hza
    have ham := hα (le_of_not_gt hza)
    have hh := (hreg z ⟨le_rfl,hz.2⟩).2
    rw [heq] at ham
    linarith
  refine ⟨hza,?_⟩
  simpa only [heq] using hreg a ⟨hza.le,ha.2⟩

 theorem constrainedFutureBand_geometry {r₀ u₀ c : ℝ} {k M : ℝ → ℝ}
    (hr : r₀≤1) (hc : 0<c) (hk : ContinuousOn k (Icc r₀ 1))
    (hkc : ∀ t ∈ Icc r₀ 1, c≤k t)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)
    (α : inverseIntegralConstraints r₀ u₀ k M)
    (p q t : Icc u₀ 1) {v B z cl cu : ℝ}
    (hv : 0<v) (hB : 0<B) (hcl : 0<cl) (hcu : 0<cu)
    (hp : p.val=B*v) (hq : q.val=2*B*v) (ht : t.val=3*B*v)
    (hz : z ∈ Icc r₀ 1) (hstart : cu*z<B*v)
    (hreg : ∀ r ∈ Icc z 1, cl*r≤α.val.val r ∧ α.val.val r≤cu*r) :
    let a := (constrainedQuantile hr hc hk hkc hm hM α p).val
    let ab := (constrainedQuantile hr hc hk hkc hm hM α q).val
    let ac := (constrainedQuantile hr hc hk hkc hm hM α t).val
    z<a ∧ a<ab ∧ ab<ac ∧ ac≤(3*B/cl)*v ∧
      ab≤(2*cu/cl)*a ∧ cl*a≤q.val-p.val ∧ q.val-p.val≤cu*a := by
  dsimp only
  let Q := constrainedQuantile hr hc hk hkc hm hM α
  have hQa : α.val.val (Q p)=p.val := constrainedQuantile_spec hr hc hk hkc hm hM α p
  have hQb : α.val.val (Q q)=q.val := constrainedQuantile_spec hr hc hk hkc hm hM α q
  have hQc : α.val.val (Q t)=t.val := constrainedQuantile_spec hr hc hk hkc hm hM α t
  have hrA := radius_in_regular_region α.val.property.2 (Q p).property hz hQa
    (by rwa [hp]) hreg
  have hrB := radius_in_regular_region α.val.property.2 (Q q).property hz hQb
    (by rw [hq]; nlinarith [mul_pos hB hv]) hreg
  have hrC := radius_in_regular_region α.val.property.2 (Q t).property hz hQc
    (by rw [ht]; nlinarith [mul_pos hB hv]) hreg
  have hpq : p<q := by change p.val<q.val; rw [hp,hq]; nlinarith [mul_pos hB hv]
  have hqt : q<t := by change q.val<t.val; rw [hq,ht]; nlinarith [mul_pos hB hv]
  have hmono : StrictMono Q := (inverseConstraintOrderIso hr hc hk hkc hm hM α).symm.strictMono
  refine ⟨hrA.1,hmono hpq,hmono hqt,?_,?_,?_,?_⟩
  · have hh := hrC.2.1
    rw [ht] at hh
    have hb : (Q t).val≤3*B*v/cl := (le_div_iff₀ hcl).mpr (by nlinarith)
    convert hb using 1
    ring
  · have ha := hrA.2.2
    have hb := hrB.2.1
    rw [hp] at ha
    rw [hq] at hb
    have ha' : B*v/cu ≤ (Q p).val := (div_le_iff₀ hcu).mpr (by nlinarith)
    calc
      (Q q).val ≤ 2*B*v/cl := (le_div_iff₀ hcl).mpr (by nlinarith)
      _ = (2*cu/cl)*(B*v/cu) := by
        field_simp
      _ ≤ (2*cu/cl)*(Q p).val := mul_le_mul_of_nonneg_left ha' (by positivity)
  · have hh := hrA.2.1
    rw [hp,hq] at *
    linarith
  · have hh := hrA.2.2
    rw [hp,hq] at *
    linarith

end SKFluctuations

end

end OAI
