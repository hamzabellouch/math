import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedBudget
import OAI.Combinatorics.KMedian.Programs.StarActivationProgram
import OAI.Combinatorics.KMedian.Rounding.SignedRoundProgram
import OAI.Combinatorics.KMedian.Programs.MaskBestProgram

namespace OAI


                                                
section
namespace MetricKMedian.SparseSignedPreparation.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table setView)
abbrev QRow := List ℚ
abbrev StateRaw := QRow × (Table × Row)
def view {n m : ℕ} (s : SparseSignedPreparation.State n m) : StateRaw :=
  (s.1.toList,(SparseGraph.ListOperation.view s.2.1,List.ofFn s.2.2))
structure KernelInput where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1
abbrev KernelRaw := List Unit × (Table × QRow)
def KernelInput.raw (x : KernelInput) : KernelRaw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),x.p.toList))
abbrev KernelInput.encode (x : KernelInput) := enc x.raw

def KernelInput.star (x : KernelInput) : SparseStarActivation.Program.Input :=
  ⟨x.n,x.m,x.D,RationalWeightedStep.point x.p,x.feasible⟩
def KernelInput.bernoulli (x : KernelInput) : SparseBernoulli.Program.Input :=
  ⟨x.m,RationalWeightedStep.point x.p,x.feasible⟩
 theorem point_list {m : ℕ} (p : Vector ℚ m) : List.ofFn (RationalWeightedStep.point p)=p.toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp [RationalWeightedStep.point]
noncomputable def starInputProgram : PolyProgram KernelInput.encode SparseStarActivation.Program.Input.encode KernelInput.star :=
  (identity enc).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseStarActivation.Program.Input.encode,SparseStarActivation.Program.Input.raw,
      KernelInput.star,point_list]; rfl)
noncomputable def bernoulliInputProgram : PolyProgram KernelInput.encode SparseBernoulli.Program.Input.encode KernelInput.bernoulli :=
  ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun x => by
    simp only [SparseBernoulli.Program.Input.encode,KernelInput.bernoulli,point_list]; rfl)
noncomputable def bernoulliProgram : PolyProgram KernelInput.encode (ed SparseBernoulli.Program.er)
    (fun x => (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
      List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
      (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)) := by
  let get : PolyProgram SparseBernoulli.Program.State.encode (ed SparseBernoulli.Program.er)
      (fun x : SparseBernoulli.Program.State => (x.raw SparseBernoulli.Program.view).2) :=
    (snd SparseBernoulli.Program.Context.encode (ed SparseBernoulli.Program.er)).recode
      (SparseIntegerLaw.DependentProgram.Bundle.raw SparseBernoulli.Program.view) (fun _ => rfl) (fun _ => rfl)
  exact (bernoulliInputProgram.comp (SparseBernoulli.Program.runStateProgram 2) |>.comp get).congr _ (fun _ => rfl)

def attach (x : QRow × Data (Table × Row)) : Data StateRaw := (x.2.1,x.2.2.map (fun s => (x.1,s)))
@[fun_prop] theorem attach_poly : Poly attach := by
  unfold attach; apply pair
  · fun_prop
  · apply list_map <;> fun_prop

def KernelInput.result (x : KernelInput) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (kernel x.D x.p x.feasible)).1,(kernel x.D x.p x.feasible).states.toList.map view)
 theorem kernel_raw (x : KernelInput) :
    attach (x.p.toList,prodData (x.star.result,
       (((SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.denominator,
         List.ofFn (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).law.numerator),
       (SparseBernoulli.run (d:=2) (RationalWeightedStep.point x.p) x.feasible x.m).states.toList.map List.ofFn)))=x.result := by
  simp only [KernelInput.star,SparseStarActivation.Program.Input.result,attach,prodData,
    KernelInput.result,kernel,SparseIntegerLaw.BinarySparse.raw,SparseIntegerLaw.prod,
    states_list,List.flatMap_def,List.map_ofFn,Function.comp_def,
    RoundingList.ofFn_product,Vector.toList_ofFn,view]
  rfl

noncomputable def kernelProgram : PolyProgram KernelInput.encode (enc : Data StateRaw → List Bool) KernelInput.result := by
  let p : PolyProgram KernelInput.encode enc (fun x : KernelInput => x.p.toList) :=
    ((snd enc enc).comp (snd enc enc)).recode KernelInput.raw (fun _ => rfl) (fun _ => rfl)
  exact (p.fanout ((starInputProgram.comp SparseStarActivation.Program.program).fanout bernoulliProgram
    |>.comp prodData_poly.program) |>.comp attach_poly.program).congr _ kernel_raw

structure Input where
  n : ℕ
  m : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  p : Vector ℚ m
  feasible : ∀ e, 0≤RationalWeightedStep.point p e ∧ RationalWeightedStep.point p e≤1
  c_unit : ∀ e, 0≤c e ∧ c e≤1
abbrev Raw := List Unit × (Table × (QRow × QRow))
def Input.raw (x : Input) : Raw :=
  (List.replicate x.n (),(List.ofFn (fun e => setView (x.D e)),(List.ofFn x.c,x.p.toList)))
abbrev Input.encode (x : Input) := enc x.raw

def Input.signed (x : Input) : RoundingProgram.Input true :=
  ⟨x.m,SparseSignedPreparation.signed x.D x.c,x.p,by simp,x.feasible⟩
def beta (x : Raw) : QRow :=
  (SparseGraph.ListOperation.indices x.2.2.1).map (fun e => x.2.2.1[e]?.getD 0-
    (Completion.Rational.BestProgram.card (x.2.1[e]?.getD []):ℚ))
@[fun_prop] theorem beta_poly : Poly beta := by unfold beta; apply list_map <;> fun_prop
 theorem beta_input (x : Input) : beta x.raw=List.ofFn (SparseSignedPreparation.signed x.D x.c) := by
  simp only [beta,Input.raw,SparseGraph.ListOperation.indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta]
  congr 1
  funext e
  rw [Completion.Rational.BestProgram.card_view]
  rfl
noncomputable def signedInputProgram : PolyProgram Input.encode RoundingProgram.Input.encode Input.signed := by
  let p : PolyProgram enc enc (fun x : Raw => (beta x,x.2.2.2)) := Poly.program (by fun_prop)
  exact p.recode Input.raw (fun _ => rfl) (fun x => by
    change enc (beta x.raw,x.p.toList)=_
    rw [beta_input]; rfl)

def Input.μ (x : Input) := SparseSignedRounding.round (SparseSignedPreparation.signed x.D x.c) x.p x.feasible
def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.D,x.μ.states[i.val],
    (SparseSignedRounding.round_invariants (SparseSignedPreparation.signed x.D x.c) x.p x.feasible (fun e _ =>
      (sub_le_self _ (Nat.cast_nonneg _)).trans (x.c_unit e).2) i).1⟩
def Input.kernels (x : Input) := List.ofFn x.ker

def inputRows (x : Raw × QRow × Data QRow) : List KernelRaw :=
  x.2.2.2.map (fun p => (x.1.1,(x.1.2.1,p)))
@[fun_prop] theorem inputRows_poly : Poly inputRows := by unfold inputRows; apply list_map <;> fun_prop
noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let s := signedInputProgram.comp RoundingProgram.SignedRound.program
  let sr : PolyProgram RoundingProgram.State.encode enc (RoundingProgram.State.raw (s:=true)) :=
    (identity enc).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (r.fanout (s.comp sr) |>.comp inputRows_poly.program).recode id (fun _ => rfl) (fun x => by
    change encodeList enc (inputRows (x.raw,(RoundingProgram.SignedRound.result x.signed).raw))=_
    simp only [inputRows,RoundingProgram.State.raw,states_list,List.map_ofFn,
      Function.comp_def]
    change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
    rw [List.ofFn_comp',encodeList_map]; rfl)

def dummy : KernelInput := ⟨0,0,Fin.elim0,#v[],fun i => Fin.elim0 i⟩
def Input.result (x : Input) : Data StateRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.p x.feasible x.c_unit)).1,
    (law x.D x.c x.p x.feasible x.c_unit).states.toList.map view)
theorem result_bind (x : Input) : x.result=
    ((SparseIntegerLaw.BinarySparse.raw (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible))).1,
      (x.μ.bindIndexed (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible)).states.toList.map view) := rfl
 theorem bind_result (x : Input) :
    bindData ((SparseIntegerLaw.BinarySparse.raw x.μ).1,x.kernels.map KernelInput.result)=x.result := by
  rw [result_bind]
  unfold Input.kernels
  simp only [List.map_ofFn,Function.comp_def,KernelInput.result,Input.ker]
  exact bindData_raw x.μ (fun i => kernel x.D (x.μ.states[i.val]) (x.ker i).feasible) view
noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) := by
  let weights : PolyProgram RoundingProgram.State.encode el (fun x : RoundingProgram.State true => (x.raw).2.1) :=
    ((snd enc enc).comp (fst enc enc)).recode RoundingProgram.State.raw RoundingProgram.State.encode_raw (fun _ => rfl)
  exact (signedInputProgram.comp RoundingProgram.SignedRound.program |>.comp weights).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data StateRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result

end MetricKMedian.SparseSignedPreparation.Program
end

end OAI
