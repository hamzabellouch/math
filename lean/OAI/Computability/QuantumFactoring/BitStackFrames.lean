import Mathlib
import OAI.Computability.QuantumFactoring.BitStackRelabel
import OAI.Computability.QuantumFactoring.BitStackProcedures

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type}
def sumStore (s : Store K) (t : Store L) : Store (K ⊕ L) := Sum.elim s t
@[simp] lemma sumStore_left (s : Store K) (t : Store L) (k : K) :
    sumStore s t (Sum.inl k)=s k := rfl
@[simp] lemma sumStore_right (s : Store K) (t : Store L) (l : L) :
    sumStore s t (Sum.inr l)=t l := rfl
lemma sumStore_empty : sumStore (fun _ : K=>[]) (fun _ : L=>[])=fun _=>[] := by
  funext j; cases j <;> rfl

def leftEmbed (K L : Type) : K ↪ K ⊕ L := ⟨Sum.inl,Sum.inl_injective⟩
lemma overlay_left (s : Store K) (t : Store L) :
    overlay (leftEmbed K L) (sumStore (fun _=>[]) t) s=sumStore s t := by
  funext j
  cases j with
  | inl j => exact overlay_at _ _ _ j
  | inr j => exact overlay_outside _ _ _ _ (by intro i; simp [leftEmbed])

variable [DecidableEq K] [DecidableEq L]
@[simp] lemma sumStore_update_left (s : Store K) (t : Store L) (k : K) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inl k) xs=sumStore (Function.update s k xs) t := by
  funext j; cases j <;> simp [Function.update,sumStore]
@[simp] lemma sumStore_update_right (s : Store K) (t : Store L) (k : L) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inr k) xs=sumStore s (Function.update t k xs) := by
  funext j; cases j <;> simp [Function.update,sumStore]
lemma sumStore_singleton_left (k : K) (xs : List Bool) :
    singletonStore (Sum.inl k) xs=sumStore (singletonStore k xs) (fun _ : L=>[]) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_left]; rfl
lemma sumStore_singleton_right (k : L) (xs : List Bool) :
    singletonStore (Sum.inr k) xs=sumStore (fun _ : K=>[]) (singletonStore k xs) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_right]; rfl
lemma Runs.left {p : Program K} {s u : Store K} {c : ℕ} (h : Runs p s u c) (t : Store L) :
    Runs (p.relabel Sum.inl) (sumStore s t) (sumStore u t) c := by
  have hh := h.relabel (leftEmbed K L) (sumStore (fun _=>[]) t)
  rw [overlay_left,overlay_left] at hh
  exact hh

namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
def congrFun (p : Procedure ea eb f) (h : ∀ a,f a=g a) : Procedure ea eb g where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [h a] using p.runs a

noncomputable def identity (ea : α→List Bool) : Procedure ea ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.skip
  bound:=1
  runs a:=⟨1,by simp,Runs.skip _⟩
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
