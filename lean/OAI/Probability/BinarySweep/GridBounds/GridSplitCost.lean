import Mathlib
import OAI.Probability.BinarySweep.GridBounds.GridSplit
import OAI.Probability.BinarySweep.GridBounds.GridProjectedMoment
import OAI.Probability.BinarySweep.YoungTheory.HookHilbertOccurrence

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

lemma left_path_address (j : Fin m) (k : Fin h) :
    leftOutsideEquiv bits j (fun i => H.position (j.castAdd n).castSucc k i)=
      (rightSlot bits (H.position 0 k),
        fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i) := by
  apply Prod.ext
  · change rightSlot bits (H.position (leftTime j.castSucc) k)=_
    exact rightSlot_leftTime bits H j.castSucc k
  · rfl

lemma right_path_address (j : Fin n) (k : Fin h) :
    rightOutsideEquiv bits j (fun i => H.position (j.natAdd m).castSucc k i)=
      (leftSlot bits (H.position (rightTime (m:=m) 0) k),
        fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i) := by
  apply Prod.ext
  · change leftSlot bits (H.position (rightTime j.castSucc) k)=_
    exact leftSlot_rightTime bits H j.castSucc k
  · rfl

lemma card_pair_fiber {K Y U : Type*} [Fintype K] {l : ℕ}
    (f : K → Y) (g : K → U) (y : Y) (u : U)
    (e : {k : K // f k=y} ≃ Fin l) :
    Fintype.card {k : K // (f k,g k)=(y,u)} =
      Fintype.card {i : Fin l // g (e.symm i).val=u} := by
  apply Fintype.card_congr
  refine { toFun := fun k => ⟨e ⟨k.val,congrArg Prod.fst k.property⟩, ?_⟩
           invFun := fun i => ⟨(e.symm i.val).val, ?_⟩
           left_inv := ?_
           right_inv := ?_ }
  · simpa only [Equiv.symm_apply_apply] using congrArg Prod.snd k.property
  · exact Prod.ext (e.symm i.val).property i.property
  · intro k; apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  · intro i; apply Subtype.ext
    exact e.apply_symm_apply i.val

lemma lineHoles_left (j : Fin m) (u : GridOutside bits (j.castAdd n)) :
    lineHoles H (j.castAdd n) u =
      lineHoles (rowFamily bits H ((leftOutsideEquiv bits j) u).1) j
        ((leftOutsideEquiv bits j) u).2 := by
  unfold lineHoles
  let y := ((leftOutsideEquiv bits j) u).1
  let v := ((leftOutsideEquiv bits j) u).2
  have he (k : Fin h) : (fun i : {i : Fin (m+n) // i≠j.castAdd n} => H.position (j.castAdd n).castSucc k i)=u ↔
      (rightSlot bits (H.position 0 k),
        fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i)=(y,v) := by
    rw [← Equiv.apply_eq_iff_eq (leftOutsideEquiv bits j),left_path_address]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  convert card_pair_fiber (fun k => rightSlot bits (H.position 0 k))
    (fun k => fun i : {i : Fin m // i≠j} => leftSlot bits (H.position (leftTime j.castSucc) k) i) y v
    (@Fintype.equivFin (RowLabels bits H y) (rowLabelsFintype bits H y)) using 1 <;>
    congr!

lemma lineHoles_right (j : Fin n) (u : GridOutside bits (j.natAdd m)) :
    lineHoles H (j.natAdd m) u =
      lineHoles (columnFamily bits H ((rightOutsideEquiv bits j) u).1) j
        ((rightOutsideEquiv bits j) u).2 := by
  unfold lineHoles
  let x := ((rightOutsideEquiv bits j) u).1
  let v := ((rightOutsideEquiv bits j) u).2
  have he (k : Fin h) : (fun i : {i : Fin (m+n) // i≠j.natAdd m} => H.position (j.natAdd m).castSucc k i)=u ↔
      (leftSlot bits (H.position (rightTime (m:=m) 0) k),
        fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i)=(x,v) := by
    rw [← Equiv.apply_eq_iff_eq (rightOutsideEquiv bits j),right_path_address]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  convert card_pair_fiber (fun k => leftSlot bits (H.position (rightTime (m:=m) 0) k))
    (fun k => fun i : {i : Fin n // i≠j} => rightSlot bits (H.position (rightTime j.castSucc) k) i) x v
    (@Fintype.equivFin (ColumnLabels bits H x) (columnLabelsFintype bits H x)) using 1 <;>
    congr!

theorem pathCost_split : pathCost H =
    (∑y, pathCost (rowFamily bits H y)) + (∑x, pathCost (columnFamily bits H x)) := by
  unfold pathCost
  rw [Fin.sum_univ_add]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [lineHoles_left]
    have he := Equiv.sum_comp (leftOutsideEquiv bits j) (fun yu =>
      Real.log (((2^leftBits bits j:ℕ):ℝ)^lineHoles (rowFamily bits H yu.1) j yu.2 /
        (Nat.descFactorial (2^leftBits bits j) (lineHoles (rowFamily bits H yu.1) j yu.2):ℝ)))
    simpa only [Fintype.sum_prod_type] using he
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp_rw [lineHoles_right]
    have he := Equiv.sum_comp (rightOutsideEquiv bits j) (fun xu =>
      Real.log (((2^rightBits bits j:ℕ):ℝ)^lineHoles (columnFamily bits H xu.1) j xu.2 /
        (Nat.descFactorial (2^rightBits bits j) (lineHoles (columnFamily bits H xu.1) j xu.2):ℝ)))
    simpa only [Fintype.sum_prod_type] using he

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed TraceHolder Density

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)
  {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

local instance : LinearOrder (GridSlot (rightBits bits)) := rowOrder bits
local instance : LinearOrder (GridSlot (leftBits bits)) := columnOrder bits
local instance : Nonempty (GridSlot (rightBits bits)) := ⟨fun _ _ => false⟩

def rowFreeSize (y : GridSlot (rightBits bits)) := Fintype.card (FreeSlot (rowFamily bits H y) 0)
def columnFreeSize (x : GridSlot (leftBits bits)) := Fintype.card (FreeSlot (columnFamily bits H x) 0)

lemma holeCount_junction :
    (Fintype.card (GridSlot (rightBits bits)):ℝ)*Fintype.card (GridSlot (leftBits bits))-
      (junctionSize bits H:ℝ)=h := by
  have hh : h≤gridSize bits := by
    have he := Fintype.card_le_of_injective (H.position 0) (H.disjoint 0)
    simpa only [Fintype.card_fin,card_gridSlot] using he
  rw [junctionSize_eq,Nat.cast_sub hh,card_gridSlot,card_gridSlot,
    size_split,Nat.cast_mul]
  ring

theorem conditional_dense_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (p : A → Bool)
    (hocc : 0<Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p (junctionSize bits H))))
    (z : ℝ) {q : ℕ} (hq : 0<q) (c : ℝ) (hc : 0≤c) (hcq : c≤q)
    (ER : GridSlot (rightBits bits) → ℝ) (EC : GridSlot (leftBits bits) → ℝ)
    (hchildR : ∀y (a : ActiveType p (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+ER y))
    (hchildC : ∀x (a : ActiveType p (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+EC x)) :
    evenMoment q (groupAverage (ρ.comp (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*Real.log (Module.finrank ℂ V:ℝ)+(∑y, ER y)+(∑x, EC x)+c*h+
        (1+4*c+2*(q:ℝ))*(Fintype.card A:ℝ)^2*
          (blockLogSize (rowFreeSize bits H)+blockLogSize (columnFreeSize bits H))) := by
  refine (conditional_le_junction bits H ρ hρ p hocc z hq).trans ?_
  have hb := grouped_dense_bound (physicalBoard bits H) p
    (groupingOrder (rowGrouping bits H)) (groupingOrder (columnGrouping bits H))
    (groupingPerm (rowGrouping bits H)) (groupingPerm (columnGrouping bits H))
    (physicalBoard_row bits H) (physicalBoard_column bits H) ρ
    (rowChildWeight bits H z) (columnChildWeight bits H z) hq c hc hcq ER EC hchildR hchildC
  rw [holeCount_junction] at hb
  exact hb

theorem conditional_hook_dense_bound {t : ℕ} (ht : 0<t)
    (α : (junctionSize bits H).Partition) (hα : Young.InHook (Young.diagram α) t)
    (z : ℝ) {q : ℕ} (hq : 0<q) (c : ℝ) (hc : 0≤c) (hcq : c≤q)
    (ER : GridSlot (rightBits bits) → ℝ) (EC : GridSlot (leftBits bits) → ℝ)
    (hchildR : ∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-c*typeF a.val+ER y))
    (hchildC : ∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-c*typeF a.val+EC x)) :
    evenMoment q (groupAverage ((Young.partitionHilbertRep α).comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-c*typeF α+(∑y, ER y)+(∑x, EC x)+c*h+
        (1+4*c+2*(q:ℝ))*(2*(t:ℝ))^2*
          (blockLogSize (rowFreeSize bits H)+blockLogSize (columnFreeSize bits H))) := by
  let : NeZero t := ⟨ne_of_gt ht⟩
  have hb := conditional_dense_bound bits H (Young.partitionHilbertRep α)
    (Young.partitionHilbertRep_unitary α) (Prod.fst : Bool × Fin t → Bool)
    (Young.hookHilbert_occurs α hα) z hq c hc hcq ER EC hchildR hchildC
  simpa only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat,typeF] using hb

end BinaryCoordinateSweeps.GridSplit

end

end OAI
