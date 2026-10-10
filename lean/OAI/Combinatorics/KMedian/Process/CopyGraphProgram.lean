import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchOrdinalArrays
import OAI.Combinatorics.KMedian.Process.TaperGraphProgram
import OAI.Combinatorics.KMedian.Process.CopyListEncoding
import OAI.Combinatorics.KMedian.Process.TaperReindex

namespace OAI


                                        
section
namespace MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Finset
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
open CopyList

structure Input where
  f : ℕ
  Δ : ℕ
  d : Fin f → Fin f → ℚ
  g : ℚ
  P : ℚ
  positive : 0<P
  A : Finset (CopyState.Copy (F:=Fin f) Δ)

abbrev Raw := (((ℚ × ℚ) × ℕ) × List (List ℚ)) × Row

def Input.raw (x : Input) : Raw := ((((x.g,x.P),x.Δ),List.ofFn (fun i => List.ofFn (x.d i))),CopyList.view x.A)
abbrev Input.encode (x : Input) := enc x.raw

def prepare (x : Raw) : TaperGraphProgram.Raw :=
  (x.1.1,(active x.2).map (fun a =>
    ((active x.2).map (fun b => ((x.1.2[a/x.1.1.2]?.getD [])[b/x.1.1.2]?.getD 0)),
     (active x.2).map (fun b => decide (b/x.1.1.2=a/x.1.1.2)))))
@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  apply pair
  · fun_prop
  · apply list_map
    · apply pair <;> (apply list_map <;> fun_prop)
    · fun_prop

 theorem rank_owner {f Δ : ℕ} (a : CopyState.Copy (F:=Fin f) Δ) :
    (rank a).val/Δ=a.1.val := by
  change (a.2.val+Δ*a.1.val)/Δ=a.1.val
  have hd : 0<Δ := Nat.zero_lt_of_lt a.2.isLt
  rw [Nat.add_comm,Nat.mul_add_div hd,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]

local instance {f Δ : ℕ} : LinearOrder (CopyState.Copy (F:=Fin f) Δ) := copyOrder
local instance {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ)) : LinearOrder ↥A := activeOrder A

def Input.taper (x : Input) : TaperGraphProgram.Input where
  n := x.A.card
  d := fun i h => x.d (enumeration x.A i).val.1 (enumeration x.A h).val.1
  own := fun i => (own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding
  g := x.g
  P := x.P
  Δ := x.Δ
  positive := x.positive

 theorem prepare_input (x : Input) : prepare x.raw=x.taper.raw := by
  dsimp only [TaperGraphProgram.Input.raw,Input.taper]
  simp only [prepare,Input.raw,active_view,List.map_ofFn,Function.comp_def,rank_owner,
    List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,
    mem_map_equiv,Equiv.symm_symm,own,mem_filter,mem_univ,true_and]
  simp only [Fin.ext_iff]
noncomputable def taperProgram : PolyProgram Input.encode TaperGraphProgram.Input.encode Input.taper :=
  prepare_poly.program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepare_input x))

 theorem taper_q (x : Input) : x.taper.qInput.q =
    (fun h i => Taper.sourceMarginals x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
      (own x.A (enumeration x.A i)) x.Δ (enumeration x.A h)) := by
  funext h i
  let e := ordinal x.A
  have hm : ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding).map e.toEquiv.toEmbedding =
      own x.A (enumeration x.A i) := by
    rw [ordinal_enum]
    ext a
    simp only [mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]
  have hh := Taper.source_reindex e x.g x.P (fun a : x.A => x.d (enumeration x.A i).val.1 a.val.1)
    ((own x.A (enumeration x.A i)).map (enumeration x.A).symm.toEmbedding) x.Δ h
  rw [hm] at hh
  exact hh.symm

def Input.law (x : Input) := graphLaw x.d x.g x.P x.A

def Input.result (x : Input) : Data Table :=
  ((x.law.law.denominator,List.ofFn x.law.law.numerator),
    x.law.states.toList.map (RationalBatchData.Ordinal.graphView (ordinal x.A)))

 theorem reindexed_lift {f Δ : ℕ} (A : Finset (CopyState.Copy (F:=Fin f) Δ))
    (G : Fin A.card → Finset (Fin A.card)) :
    RationalBatchData.Ordinal.graphView (ordinal A) (SparseEnumeratedGraph.lift (enumeration A) G)=
      SparseGraph.ListOperation.view G := by
  simp only [RationalBatchData.Ordinal.graphView,RationalBatchData.Ordinal.sets_eq,
    SparseGraph.ListOperation.view]
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [SparseEnumeratedGraph.mem_lift]
  change (enumeration A).symm (enumeration A h)∈G ((enumeration A).symm (enumeration A i)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]

 theorem result_eq (x : Input) : x.taper.qInput.result=x.result := by
  unfold Input.result Input.law graphLaw SparseEnumeratedGraph.law
  simp only [SparseIntegerLaw.map,Vector.toList_map,List.map_map,Function.comp_def,reindexed_lift]
  unfold SparseGraph.Program.QInput.result
  rw [taper_q]
  rfl

noncomputable def program : PolyProgram Input.encode (ed SparseGraph.ListOperation.et) Input.result :=
  (taperProgram.comp TaperGraphProgram.program).congr _ result_eq

end MetricKMedian.RationalPhysicalKernel.CopyGraphProgram
end

end OAI
