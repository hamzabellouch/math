import OAI.Analysis.LipschitzHilbert.Geometry.SelectedFarOverlap

namespace OAI

/-! Ordered overlap sums for an actual finite selection list. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
namespace LipschitzHilbert
variable {ι : Type*} [DecidableEq ι]

def orderedPairSum (f : ι → ι → ℝ≥0∞) : List ι → ℝ≥0∞
  | [] => 0
  | i::l => (∑ j ∈ l.toFinset, f i j)+orderedPairSum f l

def previousPairSum (f : ι → ι → ℝ≥0∞) (p : Finset ι) (l : List ι) : ℝ≥0∞ :=
  ∑ j ∈ l.toFinset, ∑ i ∈ p, f i j

def overlapPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  volume ((R i).carrier ∩ (R j).carrier)

def nearPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  if (R j).long*dist ((R i).axes 0) ((R j).axes 0) ≤ 64*(R j).short then overlapPair R i j else 0

def farPair (R : ι → Rectangle) (i j : ι) : ℝ≥0∞ :=
  if 64*(R j).short < (R j).long*dist ((R i).axes 0) ((R j).axes 0) then overlapPair R i j else 0

omit [DecidableEq ι] in
theorem overlapPair_split (R : ι → Rectangle) (i j : ι) :
    overlapPair R i j = nearPair R i j+farPair R i j := by
  by_cases h : (R j).long*dist ((R i).axes 0) ((R j).axes 0) ≤ 64*(R j).short
  · simp only [nearPair,farPair,ite_eq_left h,ite_eq_right (not_lt_of_ge h),add_zero]
  · simp only [nearPair,farPair,ite_eq_right h,ite_eq_left (lt_of_not_ge h),zero_add]

theorem orderedPairSum_split (f g : ι → ι → ℝ≥0∞) (l : List ι) :
    orderedPairSum (fun i j => f i j+g i j) l = orderedPairSum f l+orderedPairSum g l := by
  induction l with
  | nil => simp [orderedPairSum]
  | cons i l ih => simp only [orderedPairSum,Finset.sum_add_distrib,ih]; ring

theorem previousPairSum_cons (f : ι → ι → ℝ≥0∞) (p : Finset ι) (i : ι) (l : List ι)
    (hi : i ∉ p) (hil : i ∉ l) :
    previousPairSum f p (i::l)+orderedPairSum f (i::l) =
      (∑ j ∈ p, f j i)+(previousPairSum f (insert i p) l+orderedPairSum f l) := by
  have hit : i ∉ l.toFinset := by simpa using hil
  simp only [previousPairSum,orderedPairSum,List.toFinset_cons,Finset.sum_insert hit,
    Finset.sum_insert hi,Finset.sum_add_distrib]
  ring

theorem list_overlap_energy (R : ι → Rectangle) (l : List ι) (hl : l.Nodup) :
    (∑ i ∈ l.toFinset, ∑ j ∈ l.toFinset, overlapPair R i j) =
      (∑ i ∈ l.toFinset, volume (R i).carrier)+2*orderedPairSum (overlapPair R) l := by
  induction l with
  | nil => simp [orderedPairSum]
  | cons i l ih =>
    have hn := List.nodup_cons.mp hl
    have hit : i ∉ l.toFinset := by simpa using hn.1
    have hsym : (∑ j ∈ l.toFinset, overlapPair R j i) = ∑ j ∈ l.toFinset, overlapPair R i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg volume (inter_comm _ _)
    have hdiag : overlapPair R i i = volume (R i).carrier := by simp [overlapPair]
    simp only [List.toFinset_cons,Finset.sum_insert hit,Finset.sum_add_distrib,orderedPairSum]
    rw [hsym,hdiag,ih hn.2]
    ring

end LipschitzHilbert

end

end OAI
