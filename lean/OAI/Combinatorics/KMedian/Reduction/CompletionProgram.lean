import Mathlib
import OAI.Combinatorics.KMedian.Reduction.CompletionMaskProgram
import OAI.Combinatorics.KMedian.Programs.GreedyPackingProgram

namespace OAI


                                         
section
namespace MetricKMedian.Completion.Rational.Program
open Finset CopyState Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram MaskOperations RationalPhysicalKernel.CopyList
local instance {f Δ : ℕ} : LinearOrder (Copy (F:=Fin f) Δ) := RationalPhysicalKernel.copyOrder

structure Input (Δ : ℕ) where
  f : ℕ
  j : ℕ
  d : Fin j → Fin f → ℚ
  R : Fin j → ℚ
  A : Finset (Copy (F:=Fin f) Δ)
  B : Fin j → Finset (Copy (F:=Fin f) Δ)
  hB : ∀ c, (B c).Nonempty
abbrev Raw := List Unit × ((List (List ℚ) × List ℚ) × (Table × Row))
def Input.raw {Δ : ℕ} (x : Input Δ) : Raw :=
  (List.replicate x.f (),((List.ofFn (fun c => List.ofFn (x.d c)),List.ofFn x.R),
    (List.ofFn (fun c => view (x.B c)),view x.A)))
def Input.encode {Δ : ℕ} (x : Input Δ) : List Bool := enc x.raw
def Input.packing {Δ : ℕ} (x : Input Δ) : PackingProgram.Input :=
  ⟨x.j,x.f*Δ,x.R,(fun c => (x.B c).map finProdFinEquiv.toEmbedding),uncovered x.d x.R x.A⟩
def packRaw (Δ : ℕ) (x : Raw) : PackingProgram.Raw :=
  ((x.2.1.2,x.2.2.1),uncoveredRaw (x.2.1,integralRaw Δ (x.1,x.2.2.2)))
@[fun_prop] theorem packRaw_poly (Δ : ℕ) : Poly (packRaw Δ) := by unfold packRaw; fun_prop
 theorem packRaw_input {Δ : ℕ} (x : Input Δ) : packRaw Δ x.raw=x.packing.raw := by
  unfold packRaw Input.raw
  dsimp only
  rw [integralRaw_view,uncoveredRaw_view]
  rfl
noncomputable def packInputProgram (Δ : ℕ) : PolyProgram (Input.encode (Δ:=Δ)) PackingProgram.Input.encode Input.packing :=
  (packRaw_poly Δ).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (packRaw_input x))

def finish (Δ : ℕ) (x : Raw × Row) : Row := (indices x.1.1).map (fun i =>
  MaskProgram.get (integralRaw Δ (x.1.1,x.1.2.2.2)) i ||
    ((indices x.2).map (fun c => MaskProgram.get x.2 c && decide (firstCopy (x.1.2.2.1[c]?.getD []) / Δ=i))).any id)
@[fun_prop] theorem finish_poly (Δ : ℕ) : Poly (finish Δ) := by
  unfold finish
  apply list_map
  · have ha : Poly (fun x : (Raw × Row) × ℕ =>
        ((indices x.1.2).map (fun c => MaskProgram.get x.1.2 c &&
          decide (firstCopy (x.1.1.2.2.1[c]?.getD []) / Δ=x.2))).any id) := by
      apply comp bool_any
      apply list_map <;> fun_prop
    exact comp bool_or (pair (list_getD_comp false (by fun_prop) (by fun_prop)) ha)
  · fun_prop
 theorem finish_input {Δ : ℕ} (x : Input Δ) :
    finish Δ (x.raw,setView (packing x.j x.packing.U x.packing.R x.packing.B))=
      setView (output x.d x.R x.A x.B x.hB) := by
  have hp := packing_map finProdFinEquiv.toEmbedding x.j (uncovered x.d x.R x.A) x.R x.B
  change finish Δ (x.raw,setView (packing x.j (uncovered x.d x.R x.A) x.R
    (fun c => (x.B c).map finProdFinEquiv.toEmbedding)))=_
  rw [hp]
  let C := packing x.j (uncovered x.d x.R x.A) x.R x.B
  change finish Δ (x.raw,setView C)=_
  unfold finish Input.raw
  dsimp only
  rw [integralRaw_view]
  simp only [List.length_replicate,indices,setView,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
    Bool.or_eq_true,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq,output,mem_union,mem_image]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨b,⟨c,rfl⟩,hc⟩
    simp only [dite_eq_left c.isLt,Option.getD_some,firstCopy_view (x.B c) (x.hB c),
      RationalPhysicalKernel.CopyGraphProgram.rank_owner,Bool.and_eq_true,decide_eq_true_eq] at hc
    exact ⟨c,hc.1,Fin.ext hc.2⟩
  · rintro ⟨c,hc,he⟩
    refine ⟨_,⟨c,rfl⟩,?_⟩
    simp only [dite_eq_left c.isLt,Option.getD_some,firstCopy_view (x.B c) (x.hB c),
      RationalPhysicalKernel.CopyGraphProgram.rank_owner,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hc,congrArg Fin.val he⟩

noncomputable def program (Δ : ℕ) : PolyProgram (Input.encode (Δ:=Δ)) (encodeList encodeBool)
    (fun x => setView (output x.d x.R x.A x.B x.hB)) := by
  let raw : PolyProgram (Input.encode (Δ:=Δ)) enc Input.raw :=
    (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (raw.fanout ((packInputProgram Δ).comp PackingProgram.program) |>.comp (finish_poly Δ).program).congr _ (finish_input)
end MetricKMedian.Completion.Rational.Program
end

end OAI
