import Mathlib
import OAI.Combinatorics.KMedian.Programs.GreedyPackingProgram
import OAI.Combinatorics.KMedian.Preparation.RationalRepresentatives

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalRepresentatives.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
open SparseGraph.ListOperation (Row Table setView indices)
open MaskProgram

structure Input where
  n : ℕ
  R : Fin n → ℚ
  d : Fin n → Fin n → ℚ
  M : ℚ
  U : Finset (Fin n)
abbrev Raw := (List ℚ × (List (List ℚ) × ℚ)) × Row
def Input.raw (x : Input) : Raw := ((List.ofFn x.R,(List.ofFn (fun i => List.ofFn (x.d i)),x.M)),setView x.U)
def Input.encode (x : Input) : List Bool := enc x.raw
abbrev Cut (x : Input) := Finset (Fin x.n) × Finset (Fin x.n)
def advance (x : Input) (s : Cut x) : Cut x :=
  if h : s.1.Nonempty then
    let c := Preparation.firstNearest s.1 x.R h
    (s.1.filter (fun i => x.M*x.R i < x.d i c),insert c s.2)
  else s
structure State where
  input : Input
  cut : Cut input
def State.raw (s : State) : Raw × (Row × Row) := (s.input.raw,(setView s.cut.1,setView s.cut.2))
def State.encode (s : State) : List Bool := enc s.raw
def State.step (s : State) : State := ⟨s.input,advance s.input s.cut⟩
def Input.state (x : Input) (t : ℕ) : State := ⟨x,(advance x)^[t] (x.U,∅)⟩
def Input.start (x : Input) := x.state 0

def stepRaw (x : Raw × (Row × Row)) : Raw × (Row × Row) :=
  if x.2.1.any id then
    let c := MaskProgram.nearest (x.1.1.1,x.2.1)
    (x.1,((indices x.2.1).map (fun i => MaskProgram.get x.2.1 i &&
      decide (x.1.1.2.2*(x.1.1.1[i]?.getD 0) < (x.1.1.2.1[i]?.getD [])[c]?.getD 0)),
      (indices x.2.2).map (fun i => MaskProgram.get x.2.2 i || decide (i=c))))
  else x
@[fun_prop] theorem stepRaw_poly : Poly stepRaw := by
  unfold stepRaw
  apply Poly.ite
  · fun_prop
  · apply pair
    · fun_prop
    · apply pair <;> apply list_map <;> fun_prop
  · fun_prop
 theorem any_view {n : ℕ} (U : Finset (Fin n)) : (setView U).any id=decide U.Nonempty := by
  apply Bool.eq_iff_iff.mpr
  simp only [setView,List.any_eq_true,List.mem_ofFn,id_eq,decide_eq_true_eq]
  constructor
  · rintro ⟨b,⟨i,rfl⟩,hi⟩; exact ⟨i,of_decide_eq_true hi⟩
  · rintro ⟨i,hi⟩; exact ⟨_,⟨i,rfl⟩,decide_eq_true hi⟩
     
 theorem stepRaw_state (s : State) : stepRaw s.raw=(s.step).raw := by
  unfold stepRaw State.raw State.step advance
  rw [any_view]
  by_cases h : s.cut.1.Nonempty
  · simp only [decide_eq_true h,ite_true,dite_eq_left h,Input.raw,nearest_view s.input.R s.cut.1 h]
    apply Prod.ext
    · rfl
    apply Prod.ext
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,
        dite_eq_left (Preparation.firstNearest _ _ h).isLt,mem_filter,Bool.decide_and]
    · simp only [indices,setView,List.length_ofFn,RoundingList.range_finRange,Function.comp_def,← List.ofFn_eq_map,List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      simp only [MaskProgram.get,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some,Fin.eta,mem_insert,Bool.decide_or]
      rw [Bool.or_comm]
      congr 1
      simp only [Fin.ext_iff]
  · simp only [decide_eq_false h,Bool.false_eq_true,ite_false,dite_eq_right h]

noncomputable def stepProgram : PolyProgram State.encode State.encode State.step :=
  stepRaw_poly.program.recode State.raw (fun _ => rfl) (fun s => congrArg enc (stepRaw_state s))
 theorem state_iterate (x : Input) (t : ℕ) : State.step^[t] x.start=x.state t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih]
    change (⟨x,advance x ((advance x)^[t] (x.U,∅))⟩ : State)=_
    simp only [Input.state,Function.iterate_succ_apply']

noncomputable def startProgram : PolyProgram Input.encode State.encode Input.start := by
  have hp : Poly (fun x : Raw => (x,(x.2,x.2.map (fun _ => false)))) := by
    apply pair
    · fun_prop
    · apply pair
      · fun_prop
      · apply list_map <;> fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (x.raw,(setView x.U,(setView x.U).map (fun _ => false)))=enc (x.raw,(setView x.U,setView ∅))
    simp only [setView,List.map_ofFn,notMem_empty,decide_false,Function.comp_def]
    rfl)
noncomputable def countProgram : PolyProgram Input.encode Nat.bits Input.n := by
  have hp : Poly (fun x : Raw => x.2.length) := by fun_prop
  exact hp.program.recode Input.raw (fun _ => rfl) (fun x => by simp only [Input.raw,setView,List.length_ofFn]; rfl)
 theorem input_bound (x : Input) : x.n≤x.encode.length := by
  have hh := EncodedList.length_le encodeBool (setView x.U)
  simp only [setView,List.length_ofFn] at hh
  have he : x.encode.length=2*(enc (x.raw.1)).length+1+(enc x.raw.2).length := encodePair_length _ _ _
  change x.n≤(enc (setView x.U)).length at hh
  change x.encode.length=2*(enc x.raw.1).length+1+(enc (setView x.U)).length at he
  omega
 theorem mask_length {n : ℕ} (U : Finset (Fin n)) : (enc (setView U)).length≤3*n := Completion.Rational.PackingProgram.mask_length U
 theorem state_size (x : Input) (t : ℕ) : (State.encode (x.state t)).length≤11*x.encode.length+2 := by
  have h1 := mask_length ((advance x)^[t] (x.U,∅)).1
  have h2 := mask_length ((advance x)^[t] (x.U,∅)).2
  have hn := input_bound x
  change (encodePair Input.encode (encodePair (encodeList encodeBool) (encodeList encodeBool))
    (x,(setView ((advance x)^[t] (x.U,∅)).1,setView ((advance x)^[t] (x.U,∅)).2))).length≤_
  rw [encodePair_length,encodePair_length]
  dsimp only at ⊢
  change (encodeList encodeBool _).length≤3*x.n at h1 h2
  omega

 theorem select_empty {n : ℕ} (t : ℕ) (R : Fin n → ℚ) (d : Fin n → Fin n → ℚ) (M : ℚ) : select d R M t ∅=∅ := by
  cases t <;> simp [select,Finset.not_nonempty_empty]
 theorem advance_result (x : Input) (t : ℕ) (s : Cut x) :
    ((advance x)^[t] s).2=s.2 ∪ select x.d x.R x.M t s.1 := by
  induction t generalizing s with
  | zero => simp only [Function.iterate_zero,Function.id_def,select,union_empty]
  | succ t ih =>
    rw [Function.iterate_succ_apply,ih]
    by_cases h : s.1.Nonempty
    · simp only [advance,dite_eq_left h,select]
      ext i
      simp only [mem_union,mem_insert]
      tauto
    · have he : s.1=∅ := not_nonempty_iff_eq_empty.mp h
      simp [advance,he,select_empty]

noncomputable def program : PolyProgram Input.encode (encodeList encodeBool)
    (fun x => setView (select x.d x.R x.M x.n x.U)) := by
  let run := stepProgram.repeatFrom startProgram countProgram X (11*X+2)
    (fun x => by simpa using input_bound x)
    (fun x t _ => by rw [state_iterate]; simpa using state_size x t)
  let out : PolyProgram State.encode (encodeList encodeBool) (fun s => setView s.cut.2) :=
    ((snd enc (encodePair (encodeList encodeBool) (encodeList encodeBool))).comp
      (snd (encodeList encodeBool) (encodeList encodeBool))).recode State.raw (fun _ => rfl) (fun _ => rfl)
  exact (run.comp out).congr _ (fun x => by
    dsimp only [Function.comp_def]
    rw [state_iterate]
    change setView (((advance x)^[x.n] (x.U,∅)).2)=_
    rw [advance_result,empty_union])
end MetricKMedian.Preparation.RationalRepresentatives.Program
end

end OAI
