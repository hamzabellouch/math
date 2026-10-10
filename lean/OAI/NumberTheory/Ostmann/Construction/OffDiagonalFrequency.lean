import OAI.NumberTheory.Ostmann.Construction.CanonicalNode
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalFrequencyEstimate
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalFrequencyWindows
import OAI.NumberTheory.Ostmann.Construction.SourcePositive

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
open Arithmetic.HistoryProductWindows InitialCoordinatesTemplate Conclusion

theorem remainingState_offDiagonal_frequency_cutoff
    (sources : SourceFamily) (b s k l : ℕ) (hl : l < k)
    (Bs BD Bz L X G tb td J : ℝ)
    (hL : 20+10*(k:ℝ)+Real.log 2 ≤ Real.sqrt (bulkSize k L))
    (giant : PrimeSource) (g : (p:ℕ) → ZMod p → ℂ) (outside : List ℕ)
    (p : ℕ) (hp : 0 < p)
    (u : SourceAssignment sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b) k) l)))
    (y : Bool → RemainingSample sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b) k) l)) giant)
    (v : Bool → ℤ) (center : ℕ → ℝ)
    (ht : |(∑h,∑i,topCenters b center h i)-(J-2*tb)| ≤ 2)
    (hc : ∀j<k,|typeCenter b j center-nominalWeight k J (stepGap BD Bz k L) j| ≤ 2)
    (hgiant : ∀i,|Real.log ((y i).1.val:ℝ)-G| ≤ 1)
    (hcellU : ∀z∈assignedSlots sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b) k) l)) u,
      |Real.log (z.value:ℝ)-center z.origin| ≤ 1)
    (hcellH : ∀i,∀z∈assignedSlots sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b) k) l)) (y i).2,
      z.role ≠ .bulk → |Real.log (z.value:ℝ)-center z.origin| ≤ 1)
    (hcut : Ostmann.smoothPartition (Real.log (p:ℝ)-G) ≠ 0)
    (hA : ∀i,actualCoefficient sources (Template.initial (2*b) k)
      (frequencyBound Bs BD Bz k L) X G g (Arithmetic.sourceStateBins b s tb td) outside l
      (remainingState sources (Template.current (Template.initial (2*b) k) l) (l+1)
        giant p u (y i) (v i)) ≠ 0)
    (r : ℤ)
    (heq : r * ((assignedSlots sources (Template.extracted (l+1)
        (Template.current (Template.initial (2*b) k) l)) u).map SmallSlot.value).prod * p =
      v false * remainingProduct sources (Template.remainder (l+1)
        (Template.current (Template.initial (2*b) k) l)) giant (y true) -
      v true * remainingProduct sources (Template.remainder (l+1)
        (Template.current (Template.initial (2*b) k) l)) giant (y false)) :
    r.natAbs ≤ frequencyBound Bs BD Bz k L (l+1) := by
  let T := Template.current (Template.initial (2*b) k) l
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let hs := fun i => assignedSlots sources (Template.remainder (l+1) T) (y i).2
  let H := fun i => halfProduct (y i).1.val (hs i)
  let U := (us.map SmallSlot.value).prod
  let a := fun i => remainingState sources T (l+1) giant p u (y i) (v i)
  let w := nominalWeight k J (stepGap BD Bz k L)
  have hu : ∀z∈us,z.role = .compensation (l+1) := assignedSlots_extracted_roles sources T (l+1) u
  have huMatch : Template.Matches (Template.extracted (l+1) T) us :=
    Template.assignedSlots_matches sources _ u
  have hhMatch : ∀i,Template.Matches (Template.remainder (l+1) T) (hs i) :=
    fun i => Template.assignedSlots_matches sources _ (y i).2
  have ha : ∀i,Template.Matches T (a i).small := fun i =>
    Template.reinsert_matches (l+1) T us (hs i) huMatch (hhMatch i)
  have hperm : ∀i,(a i).small.Perm (us++hs i) := fun i =>
    Template.reinsert_perm (l+1) T us (hs i)
      (assignedSlots_length sources _ u) (assignedSlots_length sources _ (y i).2)
  have hq : ∀i,0 < (y i).1.val := fun i => (giant.prime _ (y i).1.property).pos
  have hhpos : ∀i,∀z∈hs i,0 < z.value := fun i z hz =>
    (assignedSlots_prime sources _ (y i).2 z hz).pos
  have hupos : ∀z∈us,0 < z.value := fun z hz => (assignedSlots_prime sources _ u z hz).pos
  have hHpos : ∀i,(0:ℝ) < H i := by
    intro i
    exact_mod_cast mul_pos (hq i) (assignedSlots_product_pos sources _ (y i).2)
  have hUpos : (0:ℝ) < U := by exact_mod_cast assignedSlots_product_pos sources _ u
  have hH : ∀i,|Real.log (H i:ℝ)-(G+(2:ℝ)^l*w l+stepGap BD Bz k L l)| ≤ nominalInheritedWidth k l := by
    intro i
    exact inherited_window_normalize b k l _ G tb J (stepGap BD Bz k L l) w center
      (actualCoefficient_remaining_window sources b s k l (frequencyBound Bs BD Bz k L)
        X G tb td g outside (a i) us (hs i) (y i).1.val center (ha i) (hA i)
        (hperm i) hu (hhMatch i) (hq i) (hhpos i) (hgiant i) (hcellH i)) ht hc
      (nominalWeight_recurrence_scaled hl J (stepGap BD Bz k L))
  have hU : |Real.log (U:ℝ)-(2:ℝ)^l*w l| ≤ nominalRemovedWidth k l :=
    removed_window_normalize b k l hl _ w center
      (integer_removed_window b k l us center hu huMatch hupos hcellU) hc
  have hv : ∀i,|(v i:ℝ)| ≤ Real.exp (frequencyBudget Bs BD Bz k L l) := by
    intro i
    apply int_le_exp_of_natAbs_le_frequencyBound
    exact (actualCoefficient_root_support sources (Template.initial (2*b) k)
      (frequencyBound Bs BD Bz k L) X G g (Arithmetic.sourceStateBins b s tb td) outside l
      (a i) (hA i)).2.2.2.2.2
  have hcut' := smoothPartition_support_subset hcut
  have hrev : (r:ℝ)*(U:ℝ)*(p:ℝ) = (v false:ℝ)*(H true:ℝ)-(v true:ℝ)*(H false:ℝ) := by
    have hh := congrArg (fun z : ℤ => (z:ℝ)) heq
    simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast,U,us,H,hs,T,remainingProduct] using hh
  apply int_natAbs_le_frequencyBound_of_exp
  refine (reversal_frequency_exp_bound r (v false) (v true) (H false) (H true) U p
    G ((2:ℝ)^l*w l) (stepGap BD Bz k L l) (frequencyBudget Bs BD Bz k L l)
    (nominalInheritedWidth k l) (nominalRemovedWidth k l)
    (hHpos false) (hHpos true) hUpos (by exact_mod_cast hp) (hv false) (hv true)
    (by have hh := (abs_le.mp (hH false)).2; linarith)
    (by have hh := (abs_le.mp (hH true)).2; linarith)
    (by have hh := (abs_le.mp hU).1; linarith)
    (by linarith [hcut'.1]) hrev).trans ?_
  exact Real.exp_le_exp.mpr (frequency_window_reserve_of_sqrt k Bs BD Bz L hL l)

end Ostmann.Construction

end

end OAI
