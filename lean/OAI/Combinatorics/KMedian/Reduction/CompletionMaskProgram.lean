import Mathlib
import OAI.Combinatorics.KMedian.Process.CopyNextProgram
import OAI.Combinatorics.KMedian.Reduction.RationalGreedyCompletion
import OAI.Combinatorics.KMedian.Programs.FinsetMaskProgram

namespace OAI


                                             
section
namespace MetricKMedian.Completion.Rational.MaskOperations
open Finset CopyState Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram RationalPhysicalKernel.CopyList
local instance {f Δ : ℕ} : LinearOrder (Copy (F:=Fin f) Δ) := RationalPhysicalKernel.copyOrder

def integralRaw (Δ : ℕ) (x : List Unit × Row) : Row :=
  (indices x.1).map (fun i => !((List.range Δ).map (fun k => !MaskProgram.get x.2 (k+Δ*i))).any id)
@[fun_prop] theorem integralRaw_poly (Δ : ℕ) : Poly (integralRaw Δ) := by
  unfold integralRaw
  apply list_map
  · apply comp bool_not
    apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem any_ofFn {n : ℕ} (b : Fin n → Bool) :
    (List.ofFn b).any id=true ↔ ∃i,b i=true := by
  simp only [List.any_eq_true,List.mem_ofFn]
  constructor
  · rintro ⟨v,⟨i,rfl⟩,h⟩; exact ⟨i,h⟩
  · rintro ⟨i,h⟩; exact ⟨_,⟨i,rfl⟩,h⟩
 theorem integralRaw_view {f Δ : ℕ} (A : Finset (Copy (F:=Fin f) Δ)) :
    integralRaw Δ (List.replicate f (),view A)=setView (integral Δ A) := by
  unfold integralRaw
  simp only [indices,List.length_replicate,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  unfold setView
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true_eq_eq_false,List.any_eq_false,decide_eq_true_eq,mem_integral]
  constructor
  · intro h a ha
    have haf : a.1=i := (mem_slots Δ i a).mp ha
    have hk : ¬(!MaskProgram.get (view A) (a.2.val+Δ*i.val))=true := by
      intro hh
      exact h _ (List.mem_ofFn.mpr ⟨a.2,rfl⟩) hh
    have hb : MaskProgram.get (view A) (rank a).val=true := by
      change MaskProgram.get (view A) (a.2.val+Δ*a.1.val)=true
      rw [haf]
      cases he : MaskProgram.get (view A) (a.2.val+Δ*i.val) <;> simp_all
    unfold MaskProgram.get at hb
    rw [RationalPhysicalKernel.CopyNext.view_get] at hb
    simpa only [rank,Equiv.symm_apply_apply,decide_eq_true_eq] using hb
  · intro h b hb hbad
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
    let a : Copy (F:=Fin f) Δ := (i,k)
    have ha : a∈A := h ((mem_slots Δ i a).mpr rfl)
    have hv : MaskProgram.get (view A) (k.val+Δ*i.val)=true := by
      change MaskProgram.get (view A) (rank a).val=true
      unfold MaskProgram.get
      rw [RationalPhysicalKernel.CopyNext.view_get]
      simpa only [Fin.eta,rank,Equiv.symm_apply_apply,decide_eq_true_eq] using ha
    rw [hv] at hbad
    cases hbad

def uncoveredRaw (x : (List (List ℚ) × List ℚ) × Row) : Row :=
  (indices x.1.2).map (fun c => !((indices x.2).map (fun i =>
    MaskProgram.get x.2 i && decide ((x.1.1[c]?.getD [])[i]?.getD 0≤5*(x.1.2[c]?.getD 0)))).any id)
@[fun_prop] theorem uncoveredRaw_poly : Poly uncoveredRaw := by
  unfold uncoveredRaw
  apply list_map
  · apply comp bool_not
    apply comp bool_any
    apply list_map <;> fun_prop
  · fun_prop
 theorem uncoveredRaw_view {f j Δ : ℕ} (d : Fin j → Fin f → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F:=Fin f) Δ)) :
    uncoveredRaw ((List.ofFn (fun c => List.ofFn (d c)),List.ofFn R),setView (integral Δ A))=
      setView (uncovered d R A) := by
  unfold uncoveredRaw
  simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext c
  apply Bool.eq_iff_iff.mpr
  simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left c.isLt,Option.getD_some,Fin.eta,
    Bool.not_eq_true_eq_eq_false,List.any_eq_false,decide_eq_true_eq,
    uncovered,mem_filter,mem_univ,true_and]
  constructor
  · intro h hh
    obtain ⟨i,hi,hd⟩ := hh
    apply h _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,id_eq,Bool.and_eq_true,decide_eq_true_eq] using And.intro hi hd
  · intro h b hb hh
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    apply h
    simp only [dite_eq_left i.isLt,Option.getD_some,id_eq,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact ⟨i,hh⟩

def firstCopy (b : Row) : ℕ := b.findIdx id
@[fun_prop] theorem firstCopy_poly : Poly firstCopy := ⟨Binary.PolyProgram.listFindIdx (Binary.PolyProgram.identity _) false⟩
 theorem firstCopy_view {f Δ : ℕ} (B : Finset (Copy (F:=Fin f) Δ)) (hB : B.Nonempty) :
    firstCopy (view B)=(rank (B.min' hB)).val := by
  have ha := min'_mem B hB
  unfold firstCopy
  rw [RationalPhysicalKernel.CopyNext.view_eq]
  apply (List.findIdx_eq (by simpa only [List.length_ofFn] using (rank (B.min' hB)).isLt)).mpr
  constructor
  · simp only [List.getElem_ofFn,id_eq]
    simpa only [Fin.eta,rank,Equiv.symm_apply_apply,decide_eq_true_eq] using ha
  · intro k hk
    have hkn : k<f*Δ := hk.trans (rank (B.min' hB)).isLt
    simp only [List.getElem_ofFn,id_eq]
    change decide (finProdFinEquiv.symm ⟨k,hkn⟩∈B)=false
    rw [decide_eq_false_iff_not]
    intro hb
    have hr :=
      @StrictMono.monotone _ _ (RationalPhysicalKernel.copyOrder (F:=Fin f) (Δ:=Δ)).toPartialOrder _ _
        RationalPhysicalKernel.CopyList.rank_strictMono
    have hm := hr (B.min'_le _ hb)
    have hm' : (rank (B.min' hB)).val≤k := by
      simpa only [rank,Equiv.apply_symm_apply,Fin.le_def] using hm
    omega

 theorem packing_map {j : ℕ} {I K : Type} [DecidableEq I] [DecidableEq K]
    (e : I ↪ K) (t : ℕ) (U : Finset (Fin j)) (R : Fin j → ℚ) (B : Fin j → Finset I) :
    packing t U R (fun c => (B c).map e)=packing t U R B := by
  induction t generalizing U with
  | zero => rfl
  | succ t ih =>
    unfold packing
    split_ifs with h
    · simp only [Finset.disjoint_map,ih]
    · rfl
end MetricKMedian.Completion.Rational.MaskOperations
end

end OAI
