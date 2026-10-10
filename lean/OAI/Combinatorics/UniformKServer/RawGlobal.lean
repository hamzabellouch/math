import Mathlib
import OAI.Combinatorics.UniformKServer.TapeController
import OAI.Combinatorics.UniformKServer.RawTape

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawGlobal
open RawTyped
abbrev S := RawControl.S×ℕ×Option (List ℕ)

def state {n k M R b : ℕ} (s : TapeController.State n k M R b) : S :=
  (RawControl.state s.localState.val,s.completed.val,s.tape.map RawTape.tape)
def initial (n k : ℕ) : S := (RawControl.initial n k (List.range k),0,none)
def chosen (s : S) (fresh : List ℕ) : List ℕ := s.2.2.getD fresh
def boundary (k R : ℕ) (s : S) (r : ℕ) : Bool :=
  RawFallback.endpoint k s.1.2.2.2.1 r && decide (s.2.1+1=R)
def label (k : ℕ) (T : List ℕ) (s : S) (r : ℕ) (fresh : List ℕ) : ℕ :=
  RawControl.label k T (chosen s fresh) s.1 r

def step (n k M R : ℕ) (T : List ℕ) (s : S) (r : ℕ) (fresh : List ℕ) : S :=
  bif boundary k R s r then initial n k else
    (RawControl.step n k M T (chosen s fresh) s.1 r,
      s.2.1+(bif RawFallback.endpoint k s.1.2.2.2.1 r then 1 else 0),some (chosen s fresh))

@[simp] theorem initial_state {n k M R b : ℕ} (hkn : k≤n) (hR : 0<R) :
    initial n k=state (TapeController.initial (M:=M) (b:=b) hR
      (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) := by
  unfold initial state TapeController.initial
  have hu : config (fun j : Fin k => (⟨j.val,lt_of_lt_of_le j.isLt hkn⟩ : Fin n))=List.range k := by
    simpa only [config] using (RawExpansion.range_eq_ofFn k).symm
  rw [←hu,RawControl.initial_state]
  rfl

@[simp] theorem chosen_state {n k M R b : ℕ} (s : TapeController.State n k M R b)
    (fresh : TapeController.Tape k M b) :
    chosen (state s) (RawTape.tape fresh)=RawTape.tape (TapeController.chosen s fresh) := by
  simp only [chosen,state,TapeController.chosen]
  cases s.tape <;> rfl

@[simp] theorem boundary_state {n k M R b : ℕ} (s : TapeController.State n k M R b) (r : Fin n) :
    boundary k R (state s) r.val=decide (TapeController.boundary s r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [boundary,Bool.and_eq_true,decide_eq_true_eq]
  change (RawFallback.endpoint k (RawMarks.bits s.localState.val.seen) r.val=true ∧
    s.completed.val+1=R)↔TapeController.boundary s r
  rw [RawFallback.endpoint_bits]
  simp only [decide_eq_true_eq,TapeController.boundary]

@[simp] theorem label_state {n k M R b : ℕ} (hk : 0<k) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    label k T (state s) r.val (RawTape.tape fresh)=
      (TapeController.choose hk (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh).val := by
  simp only [label,chosen_state]
  apply RawControl.label_state
  exact RawTape.tracking hk T hT s.localState.val s.localState.property r _

@[simp] theorem step_state {n k M R b : ℕ} (hk : 0<k) (hkn : k≤n) (hR : 0<R) (T : List ℕ)
    (hT : RawCertificate.rowsOK n k (horizon k M) b T=true)
    (s : TapeController.State n k M R b) (r : Fin n) (fresh : TapeController.Tape k M b) :
    step n k M R T (state s) r.val (RawTape.tape fresh)=
      state (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT) s r fresh) := by
  simp only [step,boundary_state,Bool.cond_decide,TapeController.step]
  by_cases h : TapeController.boundary s r
  · simp only [ite_eq_left h,dite_eq_left h]
    exact initial_state hkn hR
  · simp only [ite_eq_right h,dite_eq_right h]
    rw [chosen_state]
    have hh:=RawControl.step_state hk M T (RawTape.tape (TapeController.chosen s fresh))
      (EpochExpectation.selector (RawRows.complete hk (horizon k M) b T) (RawRows.total hk hT)
        (EpochExpectation.extend (TapeController.chosen s fresh))) s.localState.val r
      (RawTape.tracking hk T hT s.localState.val s.localState.property r _)
    change (RawControl.step n k M T _ (RawControl.state s.localState.val) r.val,_,_)=_
    rw [hh]
    simp only [state,RawControl.state,RawFallback.endpoint_bits,Bool.cond_decide,Option.map_some,
      EpochControl.boundedStep]

section Primitive
open Primrec
variable {α : Type*} [Primcodable α]
@[fun_prop] theorem primitive_initial (n k : α→ℕ) (hn : Primrec n) (hk : Primrec k) :
    Primrec (fun x=>initial (n x) (k x)) := by unfold initial;fun_prop
@[fun_prop] theorem primitive_chosen (s : α→S) (f : α→List ℕ) (hs : Primrec s) (hf : Primrec f) :
    Primrec (fun x=>chosen (s x) (f x)) := by
  unfold chosen
  exact Primrec.option_getD.comp (by fun_prop) hf
@[fun_prop] theorem primitive_boundary (k R : α→ℕ) (s : α→S) (r : α→ℕ)
    (hk : Primrec k) (hR : Primrec R) (hs : Primrec s) (hr : Primrec r) :
    Primrec (fun x=>boundary (k x) (R x) (s x) (r x)) := by unfold boundary;fun_prop
@[fun_prop] theorem primitive_label (k : α→ℕ) (T : α→List ℕ) (s : α→S) (r : α→ℕ) (f : α→List ℕ)
    (hk : Primrec k) (hT : Primrec T) (hs : Primrec s) (hr : Primrec r) (hf : Primrec f) :
    Primrec (fun x=>label (k x) (T x) (s x) (r x) (f x)) := by unfold label;fun_prop
@[fun_prop] theorem primitive_step (n k M R : α→ℕ) (T : α→List ℕ) (s : α→S) (r : α→ℕ) (f : α→List ℕ)
    (hn : Primrec n) (hk : Primrec k) (hM : Primrec M) (hR : Primrec R)
    (hT : Primrec T) (hs : Primrec s) (hr : Primrec r) (hf : Primrec f) :
    Primrec (fun x=>step (n x) (k x) (M x) (R x) (T x) (s x) (r x) (f x)) := by
  unfold step
  apply Primrec.cond (by fun_prop) (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair
  · exact Primrec.nat_add.comp (by fun_prop) (Primrec.cond (by fun_prop) (by fun_prop) (by fun_prop))
  · exact Primrec.option_some.comp (by fun_prop)
end Primitive
end UniformKServer.RawGlobal

end


end

end OAI
