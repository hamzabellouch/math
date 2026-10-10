import Mathlib
import OAI.Probability.SKFluctuations.ClockMassIntegral

namespace OAI

/-! Clock Split Steps. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]
attribute [local instance] Classical.propDecidable

 def splitClockSteps (u : ℝ) : List (GaussianStep ι) → List (GaussianStep ι) × List (GaussianStep ι)
  | [] => ([],[])
  | s::L => if s.1≤u then (s::(splitClockSteps u L).1,(splitClockSteps u L).2) else ([],s::L)

 omit [Fintype ι] in
 theorem splitClockSteps_append (u : ℝ) (L : List (GaussianStep ι)) :
    (splitClockSteps u L).1++(splitClockSteps u L).2=L := by
  induction L with
  | nil => rfl
  | cons s L ih => simp only [splitClockSteps]; split_ifs <;> simp only [List.cons_append,ih,List.nil_append]

 omit [Fintype ι] in
 theorem splitClockSteps_ordered (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    {a : ℝ} (L : List (GaussianStep ι)) (hL : OrderedSteps a L) (hau : a≤u) :
    OrderedSteps a (splitClockSteps u L).1 ∧ OrderedSteps u (splitClockSteps u L).2 ∧
      ∀ s ∈ (splitClockSteps u L).1, s.1≤u := by
  induction L generalizing a with
  | nil => exact ⟨hL,hu,by simp [splitClockSteps]⟩
  | cons s L ih =>
    dsimp only [splitClockSteps]
    split_ifs with hs
    · obtain ⟨ha,hb,hc⟩ := ih hL.2.2.2 hs
      refine ⟨⟨hL.1,hL.2.1,hL.2.2.1,ha⟩,hb,?_⟩
      intro t ht
      exact (List.mem_cons.mp ht).elim (fun he => he ▸ hs) (hc t)
    · exact ⟨⟨hL.1,hau.trans hu.2⟩,⟨hu.1,(le_of_not_ge hs),hL.2.2⟩,by simp⟩

 omit [Fintype ι] in
 theorem massStepFunction_split_index (u : ℝ) (L : List (GaussianStep ι))
    (hp : ∀ s ∈ L, 0<s.1) (f : ℕ → ℝ) :
    massStepFunction (positiveStepMasses L hp) f u = f (splitClockSteps u L).1.length := by
  induction L generalizing f with
  | nil => rfl
  | cons s L ih =>
    simp only [positiveStepMasses,massStepFunction,splitClockSteps]
    by_cases hs : s.1≤u
    · rw [ite_eq_left hs,ite_eq_right (not_lt.mpr hs)]
      simpa only [List.length_cons,Nat.add_comm] using ih (fun t ht => hp t (List.mem_cons_of_mem s ht)) (fun j => f (j+1))
    · rw [ite_eq_right hs,ite_eq_left (lt_of_not_ge hs)]
      rfl

 omit [Fintype ι] in
 theorem stepClockFunction_split (q₀ : ι → ℝ) (u : ℝ) (L : List (GaussianStep ι))
    {a : ℝ} (hL : OrderedSteps a L) :
    stepClockFunction q₀ L u=stepClockValues q₀ (splitClockSteps u L).1 (splitClockSteps u L).1.length := by
  induction L generalizing q₀ a with
  | nil => funext i; simp [stepClockFunction,splitClockSteps,stepClockValues]
  | cons s L ih =>
    funext i
    rw [stepClockFunction_cons]
    dsimp only [splitClockSteps]
    split_ifs with hs
    · simpa only [List.length_cons,stepClockValues] using
        congr_fun (ih (fun i => q₀ i+s.2 i) hL.2.2.2) i
    · exact stepClockFunction_before q₀ hL.2.2.2 (lt_of_not_ge hs) i

 def stepPairMoment [Nonempty ι] (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι)) (hp : ∀ s ∈ L, 0<s.1)
    (P : S → S → ℝ) (u : ℝ) : ℝ :=
  massStepFunction (positiveStepMasses L hp) (fun j => cumulativePair w φ
    (positiveStepMasses L hp) (stepClockValues (fun i => (q₀ i:ℝ)) L) j P) u

 theorem stepPairMoment_eq_split [Nonempty ι] {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0)
    (L : List (GaussianStep ι)) (hL : OrderedSteps 0 L) (P : S → S → ℝ) (u : ℝ) :
    stepPairMoment w φ q₀ L hL.mem_pos P u=
      stepPairDisorder w φ q₀ (splitClockSteps u L).1 (splitClockSteps u L).2 P 0 := by
  let A := (splitClockSteps u L).1
  let B := (splitClockSteps u L).2
  have hab : A++B=L := splitClockSteps_append u L
  have ho : OrderedSteps 0 (A++B) := hab.symm ▸ hL
  have hA : ∀ s ∈ A, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_left _ hs)
  have hB : ∀ s ∈ B, 0<s.1 := fun s hs => ho.mem_pos s (List.mem_append_right _ hs)
  have hc := ClockTree.pairDisorder_coordinates hw φ A B hA hB ho q₀ P
  dsimp only at hc
  have hm : positiveStepMasses A hA++positiveStepMasses B hB=positiveStepMasses L hL.mem_pos := by
    rw [←positiveStepMasses_append A B hA hB]
    simp only [hab]
  have he := congr_fun hc 0
  rw [hm,positiveStepMasses_length] at he
  simp only [hab] at he
  unfold stepPairMoment
  rw [massStepFunction_split_index]
  exact he

 omit [Nonempty S] in
 theorem stepPairMoment_intervalIntegrable [Nonempty ι] (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q₀ : ι → ℝ≥0) (L : List (GaussianStep ι))
    (hp : ∀ s ∈ L, 0<s.1) (P : S → S → ℝ) (a b : ℝ) :
    IntervalIntegrable (stepPairMoment w φ q₀ L hp P) volume a b :=
  massStepFunction_intervalIntegrable _ _ _ _

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def partitionValues (q : ℝ → ℝ) : ℝ → List PositiveMass → ℕ → ℝ
  | a,[],_ => q a
  | a,_::_,0 => q a
  | _,b::bs,j+1 => partitionValues q b.val bs j

 def partitionSample (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) (u : ℝ) : ℝ :=
  massStepFunction as (partitionValues q a as) u

 theorem partitionSample_nil (q : ℝ → ℝ) (a u : ℝ) :
    partitionSample q a [] u=q a := rfl

 theorem partitionSample_cons (q : ℝ → ℝ) (a : ℝ) (b : PositiveMass)
    (bs : List PositiveMass) (u : ℝ) :
    partitionSample q a (b::bs) u = if u<b.val then q a else partitionSample q b.val bs u := rfl

 theorem partitionSample_intervalIntegrable (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass)
    (c d : ℝ) : IntervalIntegrable (partitionSample q a as) volume c d :=
  massStepFunction_intervalIntegrable _ _ _ _

 def PartitionMesh (h a : ℝ) : List PositiveMass → Prop
  | [] => 1-a ≤ h
  | b::bs => b.val-a ≤ h ∧ PartitionMesh h b.val bs

 theorem partition_error_on_cell {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in a..b, |q u-q a|) ≤ (b-a)*(q b-q a) := by
  have hi : IntervalIntegrable q volume a b :=
    (hq.mono (by simpa only [uIcc_of_le hab] using
      (show Icc a b ⊆ Icc (0:ℝ) 1 from fun u hu => ⟨ha.trans hu.1,hu.2.trans hb⟩))).intervalIntegrable
  have hm : ∀ u ∈ Icc a b, |q u-q a| ≤ q b-q a := by
    intro u hu
    have h₀ := hq ⟨ha,hab.trans hb⟩ ⟨ha.trans hu.1,hu.2.trans hb⟩ hu.1
    have h₁ := hq ⟨ha.trans hu.1,hu.2.trans hb⟩ ⟨ha.trans hab,hb⟩ hu.2
    rw [abs_of_nonneg (sub_nonneg.mpr h₀)]
    linarith
  calc
    _ ≤ ∫ _ in a..b, (q b-q a) := intervalIntegral.integral_mono_on hab
      ((hi.sub intervalIntegrable_const).abs) intervalIntegrable_const hm
    _ = _ := by simp [intervalIntegral.integral_const]; ring

 theorem partitionSample_l1_error {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1))
    {a h : ℝ} (as : List PositiveMass) (ho : MassOrdered a as) (hm : PartitionMesh h a as) :
    (∫ u in a..1, |q u-partitionSample q a as u|) ≤ h*(q 1-q a) := by
  have hsub : uIcc a 1 ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le ((massOrdered_bounds ho).2)]
    exact fun u hu => ⟨(massOrdered_bounds ho).1.trans hu.1,hu.2⟩
  have hall : IntervalIntegrable q volume a 1 := (hq.mono hsub).intervalIntegrable
  induction as generalizing a with
  | nil =>
    simp only [partitionSample_nil]
    exact (partition_error_on_cell hq ho.1 ho.2 le_rfl).trans
      (mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr (hq ⟨ho.1,ho.2⟩ ⟨by norm_num,le_rfl⟩ ho.2)))
  | cons b bs ih =>
    have ha := massOrdered_bounds ho
    have hb := massOrdered_bounds ho.2.2
    have hq₀ : IntervalIntegrable q volume a b.val := hall.mono_set
      (by rw [uIcc_of_le ho.2.1,uIcc_of_le ha.2]; exact Icc_subset_Icc_right hb.2)
    have hq₁ : IntervalIntegrable q volume b.val 1 := hall.mono_set
      (by rw [uIcc_of_le hb.2,uIcc_of_le ha.2]; exact Icc_subset_Icc_left ho.2.1)
    rw [← intervalIntegral.integral_add_adjacent_intervals
      ((hq₀.sub (partitionSample_intervalIntegrable q a (b::bs) a b.val)).abs)
      ((hq₁.sub (partitionSample_intervalIntegrable q a (b::bs) b.val 1)).abs)]
    have he₀ : (∫ u in a..b.val, |q u-partitionSample q a (b::bs) u|) =
        ∫ u in a..b.val, |q u-q a| :=
      intervalIntegral.integral_congr_Ioo_of_le ho.2.1
        (fun u hu => by rw [partitionSample_cons,ite_eq_left hu.2])
    have he₁ : (∫ u in b.val..1, |q u-partitionSample q a (b::bs) u|) =
        ∫ u in b.val..1, |q u-partitionSample q b.val bs u| :=
      intervalIntegral.integral_congr_Ioo_of_le hb.2
        (fun u hu => by rw [partitionSample_cons,ite_eq_right (not_lt.mpr hu.1.le)])
    rw [he₀,he₁]
    have h₀ := (partition_error_on_cell hq ha.1 ho.2.1 hb.2).trans
      (mul_le_mul_of_nonneg_right hm.1 (sub_nonneg.mpr (hq ha hb ho.2.1)))
    have h₁ := ih ho.2.2 hm.2 (by
      rw [uIcc_of_le hb.2]
      exact fun u hu => ⟨hb.1.trans hu.1,hu.2⟩) hq₁
    calc
      _ ≤ h*(q b.val-q a)+h*(q 1-q b.val) := add_le_add h₀ h₁
      _ = _ := by ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def uniformMassTail (h : ℝ) (hh : 0<h) : ℕ → ℕ → List PositiveMass
  | _,0 => []
  | k,n+1 => ⟨(k+1:ℕ)*h,mul_pos (by positivity) hh⟩::uniformMassTail h hh (k+1) n

 theorem uniformMassTail_ordered {h : ℝ} (hh : 0<h) (k n : ℕ)
    (he : (k+n:ℕ)*h=1) : MassOrdered ((k:ℝ)*h) (uniformMassTail h hh k n) := by
  induction n generalizing k with
  | zero =>
    simp only [Nat.add_zero] at he
    exact ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,he.le⟩
  | succ n ih =>
    have ht : (k+1+n:ℕ)*h=1 := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le,?_,ih (k+1) ht⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hh.le

 theorem uniformMassTail_mesh {h : ℝ} (hh : 0<h) (k n : ℕ)
    (he : (k+n:ℕ)*h=1) : PartitionMesh h ((k:ℝ)*h) (uniformMassTail h hh k n) := by
  induction n generalizing k with
  | zero =>
    simp only [Nat.add_zero] at he
    change 1-(k:ℝ)*h ≤ h
    rw [he,sub_self]
    exact hh.le
  | succ n ih =>
    have ht : (k+1+n:ℕ)*h=1 := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he
    refine ⟨?_,ih (k+1) ht⟩
    change ((k+1:ℕ):ℝ)*h-(k:ℝ)*h ≤ h
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith

 def uniformMasses (n : ℕ) : List PositiveMass :=
  uniformMassTail ((n+1:ℕ):ℝ)⁻¹ (by positivity) 0 (n+1)

 theorem uniformMasses_ordered (n : ℕ) : MassOrdered 0 (uniformMasses n) := by
  have hh := uniformMassTail_ordered (show 0<((n+1:ℕ):ℝ)⁻¹ by positivity) 0 (n+1)
    (by simp only [Nat.zero_add]; exact mul_inv_cancel₀ (by positivity))
  simpa [uniformMasses] using hh

 theorem uniformMasses_mesh (n : ℕ) : PartitionMesh ((n+1:ℕ):ℝ)⁻¹ 0 (uniformMasses n) := by
  have hh := uniformMassTail_mesh (show 0<((n+1:ℕ):ℝ)⁻¹ by positivity) 0 (n+1)
    (by simp only [Nat.zero_add]; exact mul_inv_cancel₀ (by positivity))
  simpa [uniformMasses] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 def sampleClockSteps (q : ℝ → ι → ℝ≥0) : ℝ → List PositiveMass → List (GaussianStep ι)
  | _,[] => []
  | a,b::bs => (b.val,fun i => q b.val i-q a i)::sampleClockSteps q b.val bs

 theorem sampleClockSteps_ordered (q : ℝ → ι → ℝ≥0) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) : OrderedSteps a (sampleClockSteps q a as) := by
  induction as generalizing a with
  | nil => exact ho
  | cons b bs ih => exact ⟨ho.1,ho.2.1,b.property,ih ho.2.2⟩

 theorem sampleClockSteps_masses (q : ℝ → ι → ℝ≥0) (a : ℝ) (as : List PositiveMass)
    (hp : ∀ s ∈ sampleClockSteps q a as, 0<s.1) :
    positiveStepMasses (sampleClockSteps q a as) hp=as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih => exact congrArg (List.cons b) (ih b.val _)

 theorem sampleClockSteps_values (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {a : ℝ} (as : List PositiveMass) (ho : MassOrdered a as) (j : ℕ) (i : ι) :
    stepClockValues (fun i => (q a i:ℝ)) (sampleClockSteps q a as) j i =
      partitionValues (fun u => (q u i:ℝ)) a as j := by
  induction as generalizing a j with
  | nil => rfl
  | cons b bs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have he : (fun i => (q a i:ℝ)+(q b.val i-q a i:ℝ≥0)) =
          (fun i => (q b.val i:ℝ)) := by
        funext i
        rw [NNReal.coe_sub ((hq i) (massOrdered_bounds ho) (massOrdered_bounds ho.2.2) ho.2.1)]
        ring
      change stepClockValues (fun i => (q a i:ℝ)+(q b.val i-q a i:ℝ≥0))
        (sampleClockSteps q b.val bs) j i = partitionValues (fun u => (q u i:ℝ)) b.val bs j
      rw [he]
      exact ih ho.2.2 j

 theorem sampleClockSteps_function (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {a : ℝ} (as : List PositiveMass) (ho : MassOrdered a as) (u : ℝ) (i : ι) :
    stepClockFunction (fun i => (q a i:ℝ)) (sampleClockSteps q a as) u i =
      partitionSample (fun u => (q u i:ℝ)) a as u := by
  rw [stepClockFunction_eq _ (sampleClockSteps_ordered q as ho),sampleClockSteps_masses]
  simp_rw [sampleClockSteps_values q hq as ho]
  rfl

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def partitionEnd : ℝ → List PositiveMass → ℝ
  | a,[] => a
  | _,b::bs => partitionEnd b.val bs

 def splitMassPartition (u : PositiveMass) : List PositiveMass → List PositiveMass × List PositiveMass
  | [] => ([u],[])
  | a::as => if a.val<u.val then
      let p := splitMassPartition u as
      (a::p.1,p.2)
    else ([u],a::as)

 theorem splitMassPartition_end (u : PositiveMass) (as : List PositiveMass) (a : ℝ) :
    partitionEnd a (splitMassPartition u as).1=u.val := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [splitMassPartition]
    split_ifs
    · exact ih b.val
    · rfl

 theorem splitMassPartition_bounds (u : PositiveMass) (as : List PositiveMass) :
    ∀ b ∈ (splitMassPartition u as).1, b.val≤u.val := by
  induction as with
  | nil => simp [splitMassPartition]
  | cons b bs ih =>
    simp only [splitMassPartition]
    split_ifs with hb
    · intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact hb.le
      · exact ih c hc
    · simp

 theorem splitMassPartition_ordered (u : PositiveMass) (hu : u.val≤1)
    {a : ℝ} (as : List PositiveMass) (ho : MassOrdered a as) (hau : a≤u.val) :
    MassOrdered a (splitMassPartition u as).1 ∧ MassOrdered u.val (splitMassPartition u as).2 := by
  induction as generalizing a with
  | nil => exact ⟨⟨ho.1,hau,u.property.le,hu⟩,⟨u.property.le,hu⟩⟩
  | cons b bs ih =>
    simp only [splitMassPartition]
    split_ifs with hb
    · obtain ⟨h₁,h₂⟩ := ih ho.2.2 hb.le
      exact ⟨⟨ho.1,ho.2.1,h₁⟩,h₂⟩
    · exact ⟨⟨ho.1,hau,u.property.le,hu⟩,⟨u.property.le,le_of_not_gt hb,ho.2.2⟩⟩

 theorem splitMassPartition_mesh (u : PositiveMass) (hu : u.val≤1)
    {a h : ℝ} (as : List PositiveMass) (ho : MassOrdered a as) (hau : a≤u.val)
    (hm : PartitionMesh h a as) :
    PartitionMesh h a ((splitMassPartition u as).1++(splitMassPartition u as).2) := by
  induction as generalizing a with
  | nil =>
    change u.val-a≤h ∧ 1-u.val≤h
    change 1-a≤h at hm
    constructor <;> linarith
  | cons b bs ih =>
    simp only [splitMassPartition]
    split_ifs with hb
    · exact ⟨hm.1,ih ho.2.2 hb.le hm.2⟩
    · exact ⟨by dsimp [PartitionMesh] at hm; linarith [hm.1],
        by exact ⟨by linarith [hm.1],hm.2⟩⟩

 theorem partitionEnd_append (a : ℝ) (as bs : List PositiveMass) :
    partitionEnd a (as++bs)=partitionEnd (partitionEnd a as) bs := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => exact ih b.val

 theorem partitionValues_terminal (q : ℝ → ℝ) (a : ℝ) (as : List PositiveMass) :
    partitionValues q a as as.length=q (partitionEnd a as) := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => exact ih b.val

 theorem sampleClockSteps_append {ι : Type*} (q : ℝ → ι → ℝ≥0)
    (a : ℝ) (as bs : List PositiveMass) :
    sampleClockSteps q a (as++bs)=sampleClockSteps q a as++sampleClockSteps q (partitionEnd a as) bs := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => exact congrArg (List.cons _) (ih b.val)

 theorem MassOrdered.append_end {a : ℝ} {as bs : List PositiveMass}
    (ha : MassOrdered a as) (hb : MassOrdered (partitionEnd a as) bs) : MassOrdered a (as++bs) := by
  induction as generalizing a with
  | nil => exact hb
  | cons b as ih => exact ⟨ha.1,ha.2.1,ih ha.2.2 hb⟩

 theorem MassOrdered.end_bounds {a : ℝ} {as : List PositiveMass}
    (ha : MassOrdered a as) : 0≤partitionEnd a as ∧ partitionEnd a as≤1 := by
  induction as generalizing a with
  | nil => exact ha
  | cons b as ih => exact ih ha.2.2

 theorem PartitionMesh.append_one {a h : ℝ} {as : List PositiveMass}
    (hh : 0≤h) (hm : PartitionMesh h a as) :
    PartitionMesh h a (as++[⟨1,by norm_num⟩]) := by
  induction as generalizing a with
  | nil => exact ⟨hm,by simpa [PartitionMesh] using hh⟩
  | cons b as ih => exact ⟨hm.1,ih hm.2⟩

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem partitionSample_pair_error {q : ℝ → ℝ} (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hm : PartitionMesh h 0 as) (hk : PartitionMesh k 0 bs) :
    (∫ u in (0:ℝ)..1, |partitionSample q 0 as u-partitionSample q 0 bs u|) ≤
      (h+k)*(q 1-q 0) := by
  have hi : IntervalIntegrable q volume 0 1 :=
    (show MonotoneOn q (uIcc (0:ℝ) 1) by simpa using hq).intervalIntegrable
  have hia := partitionSample_intervalIntegrable q 0 as 0 1
  have hib := partitionSample_intervalIntegrable q 0 bs 0 1
  calc
    _ ≤ ∫ u in (0:ℝ)..1, (|q u-partitionSample q 0 as u|+|q u-partitionSample q 0 bs u|) :=
      intervalIntegral.integral_mono_on (by norm_num) (hia.sub hib).abs
        ((hi.sub hia).abs.add (hi.sub hib).abs) (fun u _ => by
          simpa only [abs_sub_comm] using abs_sub_le (partitionSample q 0 as u) (q u) (partitionSample q 0 bs u))
    _ = (∫ u in (0:ℝ)..1, |q u-partitionSample q 0 as u|)+
        (∫ u in (0:ℝ)..1, |q u-partitionSample q 0 bs u|) :=
      intervalIntegral.integral_add (hi.sub hia).abs (hi.sub hib).abs
    _ ≤ h*(q 1-q 0)+k*(q 1-q 0) :=
      add_le_add (partitionSample_l1_error hq as ha hm) (partitionSample_l1_error hq bs hb hk)
    _ = _ := by ring

 def sampledDisorderPressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q : ℝ → ι → ℝ≥0) (as : List PositiveMass) (x : ι → ℝ) : ℝ :=
  stepDisorderPressure w φ C (q 0) (sampleClockSteps q 0 as) x

 def clockVariationBound (D : ι → ℝ) (q : ℝ → ι → ℝ≥0) : ℝ :=
  (1/2:ℝ)*∑ i, (D i)^2*((q 1 i:ℝ)-(q 0 i:ℝ))

 theorem clockVariationBound_nonneg (D : ι → ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1)) :
    0 ≤ clockVariationBound D q := by
  unfold clockVariationBound
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg ?_)
  intro i _
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (by exact_mod_cast
    ((hq i) (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num))))

 theorem sampledDisorderPressure_mesh_comparison [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hm : PartitionMesh h 0 as) (hk : PartitionMesh k 0 bs) (x : ι → ℝ) :
    |sampledDisorderPressure w φ C q as x-sampledDisorderPressure w φ C q bs x| ≤
      (h+k)*clockVariationBound D q := by
  have ht := stepDisorderPressure_l1_comparison hw φ C D hC hD (q 0) (q 0)
    (sampleClockSteps q 0 as) (sampleClockSteps q 0 bs)
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb) x
  simp_rw [sampleClockSteps_function q hq as ha,sampleClockSteps_function q hq bs hb] at ht
  apply ht.trans
  calc
    _ ≤ (1/2:ℝ)*∑ i, (D i)^2*((h+k)*((q 1 i:ℝ)-(q 0 i:ℝ))) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum _) (by norm_num)
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply partitionSample_pair_error _ as bs ha hb hm hk
      intro u hu v hv huv
      exact_mod_cast (hq i) hu hv huv
    _ = _ := by
      unfold clockVariationBound
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 omit [Fintype ι] [Nonempty ι] in
 theorem sampleClockSteps_length (q : ℝ → ι → ℝ≥0) (a : ℝ) (as : List PositiveMass) :
    (sampleClockSteps q a as).length=as.length := by
  induction as generalizing a with
  | nil => rfl
  | cons b as ih => exact congrArg Nat.succ (ih b.val)

 omit [Fintype ι] [Nonempty ι] in
 theorem sampleClockSteps_terminal (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (a : ℝ) (as : List PositiveMass) (ha : MassOrdered a as) :
    stepClockValues (fun i => (q a i:ℝ)) (sampleClockSteps q a as) (sampleClockSteps q a as).length=
      (fun i => (q (partitionEnd a as) i:ℝ)) := by
  funext i
  rw [sampleClockSteps_length,sampleClockSteps_values q hq as ha,partitionValues_terminal]

 omit [Fintype ι] [Nonempty ι] in
 theorem sampleClockSteps_mass_le (q : ℝ → ι → ℝ≥0) (a : ℝ) (as : List PositiveMass)
    {u : ℝ} (hu : ∀ b ∈ as, b.val≤u) :
    ∀ s ∈ sampleClockSteps q a as, s.1≤u := by
  induction as generalizing a with
  | nil => simp [sampleClockSteps]
  | cons b as ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl|hs
    · exact hu b (by simp)
    · exact ih b.val (fun c hc => hu c (by simp [hc])) s hs

 omit [Nonempty ι] in
 theorem sampleClock_distance_integral (D : ι → ℝ) (q : ℝ → ι → ℝ≥0)
    (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as bs : List PositiveMass) (ha : MassOrdered 0 as) (hb : MassOrdered 0 bs)
    {h k : ℝ} (hm : PartitionMesh h 0 as) (hk : PartitionMesh k 0 bs) :
    (∫ u in (0:ℝ)..1, clockCoordinateDistance D
        (fun i => partitionSample (fun u => (q u i:ℝ)) 0 as u)
        (fun i => partitionSample (fun u => (q u i:ℝ)) 0 bs u)) ≤
      2*(h+k)*clockVariationBound D q := by
  unfold clockCoordinateDistance
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_mul_const]
    calc
      _ ≤ ∑ i, ((h+k)*((q 1 i:ℝ)-(q 0 i:ℝ)))*(D i)^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply partitionSample_pair_error _ as bs ha hb hm hk
        intro u hu v hv huv
        exact_mod_cast (hq i) hu hv huv
      _ = _ := by
        unfold clockVariationBound
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · intro i _
    exact ((partitionSample_intervalIntegrable _ _ _ _ _).sub
      (partitionSample_intervalIntegrable _ _ _ _ _)).abs.mul_const _

 def sampledPairDisorder (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (q : ℝ → ι → ℝ≥0) (u : ℝ) (as bs : List PositiveMass) (P : S → S → ℝ) (x : ι → ℝ) : ℝ :=
    stepPairDisorder w φ (q 0) (sampleClockSteps q 0 as) (sampleClockSteps q u bs) P x

 theorem sampledPairDisorder_mesh_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    {u : ℝ} (hu : 0≤u) (as bs cs es : List PositiveMass)
    (ha : MassOrdered 0 as) (hb : MassOrdered u bs) (hc : MassOrdered 0 cs) (he : MassOrdered u es)
    (hau : ∀ a ∈ as, a.val≤u) (hcu : ∀ c ∈ cs, c.val≤u)
    (heA : partitionEnd 0 as=u) (heC : partitionEnd 0 cs=u)
    (hetB : partitionEnd u bs=1) (hetE : partitionEnd u es=1)
    {h k : ℝ} (hmesh : PartitionMesh h 0 (as++bs)) (kmesh : PartitionMesh k 0 (cs++es))
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |sampledPairDisorder w φ q u as bs P x-sampledPairDisorder w φ q u cs es P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*(2*(h+k)*clockVariationBound D q) := by
  have hoa : MassOrdered 0 (as++bs) := ha.append_end (heA.symm ▸ hb)
  have hoc : MassOrdered 0 (cs++es) := hc.append_end (heC.symm ▸ he)
  have ht := stepPairDisorder_l1_comparison hw φ D hD hφ (q 0) (q 0)
    (sampleClockSteps q 0 as) (sampleClockSteps q u bs)
    (sampleClockSteps q 0 cs) (sampleClockSteps q u es) hu
    (sampleClockSteps_ordered q as ha) (sampleClockSteps_ordered q bs hb)
    (sampleClockSteps_ordered q cs hc) (sampleClockSteps_ordered q es he)
    (sampleClockSteps_mass_le q 0 as hau) (sampleClockSteps_mass_le q 0 cs hcu) P hK hP x
  rw [sampleClockSteps_terminal q hq 0 as ha,sampleClockSteps_terminal q hq 0 cs hc,heA,heC] at ht
  have hAB : sampleClockSteps q 0 as++sampleClockSteps q u bs=sampleClockSteps q 0 (as++bs) := by
    rw [sampleClockSteps_append,heA]
  have hCE : sampleClockSteps q 0 cs++sampleClockSteps q u es=sampleClockSteps q 0 (cs++es) := by
    rw [sampleClockSteps_append,heC]
  rw [hAB,hCE,sampleClockSteps_terminal q hq 0 (as++bs) hoa,
    sampleClockSteps_terminal q hq 0 (cs++es) hoc,
    partitionEnd_append,partitionEnd_append,heA,heC,hetB,hetE] at ht
  simp only [clockCoordinateDistance,sub_self,abs_zero,zero_mul,Finset.sum_const_zero,zero_add,add_zero] at ht
  simp_rw [sampleClockSteps_function q hq _ hoa,sampleClockSteps_function q hq _ hoc] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left
    (sampleClock_distance_integral D q hq (as++bs) (cs++es) hoa hoc hmesh kmesh)
    (mul_nonneg (ClockTree.errorJetVariation_nonneg 2 0 0) hK))

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [Fintype S]

 theorem uniformMasses_mesh_tendsto :
    Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹) atTop (𝓝 0) := by
  simpa only [Nat.cast_add,Nat.cast_one,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

 theorem sampledDisorderPressure_cauchy [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (x : ι → ℝ) :
    CauchySeq (fun k => sampledDisorderPressure w φ C q (uniformMasses k) x) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)⁻¹*clockVariationBound D q)
      atTop (𝓝 0) := by
    simpa using uniformMasses_mesh_tendsto.mul_const (clockVariationBound D q)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N,fun n hn m hm => ?_⟩
  rw [Real.dist_eq]
  have hb := sampledDisorderPressure_mesh_comparison hw φ C D hC hD q hq
    (uniformMasses n) (uniformMasses m) (uniformMasses_ordered n) (uniformMasses_ordered m)
    (uniformMasses_mesh n) (uniformMasses_mesh m) x
  exact hb.trans_lt (by nlinarith [hN n hn,hN m hm])

 def pathDisorderPressure (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C : ι → ℝ) (q : ℝ → ι → ℝ≥0) (x : ι → ℝ) : ℝ :=
  limUnder atTop (fun k => sampledDisorderPressure w φ C q (uniformMasses k) x)

 theorem sampledDisorderPressure_tendsto [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (x : ι → ℝ) :
    Tendsto (fun k => sampledDisorderPressure w φ C q (uniformMasses k) x) atTop
      (𝓝 (pathDisorderPressure w φ C q x)) :=
  (sampledDisorderPressure_cauchy hw φ C D hC hD q hq x).tendsto_limUnder

 theorem sampledDisorderPressure_path_error [Nonempty S] [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q : ℝ → ι → ℝ≥0) (hq : ∀ i, MonotoneOn (fun u => q u i) (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) {h : ℝ} (hm : PartitionMesh h 0 as)
    (x : ι → ℝ) :
    |sampledDisorderPressure w φ C q as x-pathDisorderPressure w φ C q x| ≤
      h*clockVariationBound D q := by
  have ha' := ((tendsto_const_nhds (x := sampledDisorderPressure w φ C q as x)).sub
    (sampledDisorderPressure_tendsto hw φ C D hC hD q hq x)).abs
  have hb' : Tendsto (fun k : ℕ => (h+((k+1:ℕ):ℝ)⁻¹)*clockVariationBound D q)
      atTop (𝓝 (h*clockVariationBound D q)) := by
    simpa using (tendsto_const_nhds.add uniformMasses_mesh_tendsto).mul_const (clockVariationBound D q)
  exact le_of_tendsto_of_tendsto ha' hb' (Eventually.of_forall fun k =>
    sampledDisorderPressure_mesh_comparison hw φ C D hC hD q hq as (uniformMasses k)
      ha (uniformMasses_ordered k) hm (uniformMasses_mesh k) x)

end SKFluctuations.Hierarchy

end

end OAI
