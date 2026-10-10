import Mathlib
import OAI.Combinatorics.KMedian.Programs.OuterLawProgram
import OAI.Combinatorics.KMedian.Preparation.PreparedKernelProgram

namespace OAI


                                          
section
namespace MetricKMedian.SparsePrepared.Program
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (setView)
structure Input where
  n : ℕ
  m : ℕ
  f : ℕ
  D : Fin m → Finset (Fin n)
  c : Fin m → ℚ
  q : Fin m → ℚ
  P : Fin n → Finset (Fin f)
  y : Fin f → ℚ
  p : Fin n → ℚ
  Δ : ℕ
  hy : ∀ i,0≤y i
  hp : ∀ j,0<p j
  hc : ∀ e,0≤c e ∧ c e≤1
  hq : ∀ e,0≤q e
abbrev Raw := BaseRaw × QRow
def Input.base (x : Input) : BaseRaw :=
  (List.ofFn (fun e => setView (x.D e)),(List.ofFn x.q,(List.ofFn (fun j => setView (x.P j)),
    (List.ofFn x.y,(List.ofFn x.p,x.Δ)))))
def Input.raw (x : Input) : Raw := (x.base,List.ofFn x.c)
abbrev Input.encode (x : Input) := enc x.raw

def Input.outer (x : Input) : SparseOuterLaw.Program.Input := ⟨x.n,x.m,x.D,x.c,x.q,x.hc,x.hq⟩
def outerData (x : Raw) : SparseOuterLaw.Program.Raw :=
  (x.1.2.2.2.2.1.map (fun _ => ()),(x.1.1,(x.2,x.1.2.1)))
@[fun_prop] theorem outerData_poly : Poly outerData := by
  unfold outerData; apply Binary.Automatic.Poly.pair
  · apply list_map <;> fun_prop
  · fun_prop
noncomputable def outerInputProgram : PolyProgram Input.encode SparseOuterLaw.Program.Input.encode Input.outer :=
  outerData_poly.program.recode Input.raw (fun _ => rfl) (fun x => by
    simp only [outerData,Input.raw,Input.base,List.map_const',List.length_ofFn,
      SparseOuterLaw.Program.Input.encode,SparseOuterLaw.Program.Input.raw,Input.outer])
def Input.μ (x : Input) := SparseOuterLaw.law x.D x.c x.q x.hc x.hq
def Input.ker (x : Input) (i : Fin x.μ.length) : KernelInput :=
  ⟨x.n,x.m,x.f,x.D,x.q,x.P,x.y,x.p,x.Δ,x.μ.states[i.val],x.hy,x.hp⟩
def Input.kernels (x : Input) := List.ofFn x.ker

def kernelRows (x : Raw × Data StateRaw) : List KernelRaw := x.2.2.map (fun z => (x.1.1,z))
@[fun_prop] theorem kernelRows_poly : Poly kernelRows := by unfold kernelRows; apply list_map <;> fun_prop
noncomputable def kernelsProgram : PolyProgram Input.encode (encodeList KernelInput.encode) Input.kernels := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  exact (r.fanout (outerInputProgram.comp SparseOuterLaw.Program.program) |>.comp kernelRows_poly.program).recode id
    (fun _ => rfl) (fun x => by
      change encodeList enc (kernelRows (x.raw,SparseOuterLaw.Program.Input.result x.outer))=_
      simp only [kernelRows,SparseOuterLaw.Program.Input.result,states_list,List.map_ofFn,Function.comp_def]
      change encodeList enc (List.ofFn (fun i => (x.ker i).raw))=encodeList KernelInput.encode x.kernels
      rw [List.ofFn_comp',RoundingProgram.encodeList_map]; rfl)
def dummy : KernelInput :=
  ⟨0,0,0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,0,(#v[],Fin.elim0,Fin.elim0),(fun i => Fin.elim0 i),(fun i => Fin.elim0 i)⟩
def Input.result (x : Input) : Data PreparedRaw :=
  ((SparseIntegerLaw.BinarySparse.raw (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq)).1,
    (law x.D x.c x.q x.Δ x.P x.y x.p x.hc x.hq).states.toList.map view)
theorem result_bind (x : Input) : x.result=
    ((SparseIntegerLaw.BinarySparse.raw (x.μ.bindIndexed (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val]))).1,
      (x.μ.bindIndexed (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val])).states.toList.map view) := rfl
theorem bind_result (x : Input) :
    bindData ((SparseIntegerLaw.BinarySparse.raw x.μ).1,x.kernels.map KernelInput.result)=x.result := by
  rw [result_bind]
  unfold Input.kernels
  simp only [List.map_ofFn,Function.comp_def,KernelInput.result,Input.ker]
  exact bindData_raw x.μ (fun i => kernel x.D x.q x.Δ x.P x.y x.p x.μ.states[i.val]) view
noncomputable def weightsProgram : PolyProgram Input.encode el (fun x => (SparseIntegerLaw.BinarySparse.raw x.μ).1) :=
  (outerInputProgram.comp SparseOuterLaw.Program.program |>.comp (fst el (encodeList enc))).congr _ (fun _ => rfl)
noncomputable def program : PolyProgram Input.encode (enc : Data PreparedRaw → List Bool) Input.result :=
  (weightsProgram.fanout (kernelsProgram.comp (kernelProgram.listMap dummy)) |>.comp bindData_poly.program).congr _ bind_result
end MetricKMedian.SparsePrepared.Program
end

end OAI
