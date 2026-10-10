import Mathlib
import OAI.Computability.QuantumFactoring.BitStackProducts
import OAI.Computability.QuantumFactoring.BitStackConstants

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def leftPublic (K L : Type) : (K ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inl i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

def rightPublic (K L : Type) : (L ⊕ Fin 2) ↪ ((K ⊕ L) ⊕ Fin 2) where
  toFun := fun k=>match k with | .inl i=>.inl (.inr i) | .inr i=>.inr i
  inj' := by intro i j h; cases i <;> cases j <;> simp_all

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
/-- A same-wire interface, even when the input and output word encodings differ. -/
noncomputable abbrev shared (p : Procedure ea eb f) : Procedure ea eb f where
  K:=p.K ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.seq (moveWord (Sum.inr 0) (Sum.inl p.input) (Sum.inr 1))
    (.seq (p.program.relabel Sum.inl)
      (moveWord (Sum.inl p.output) (Sum.inr 0) (Sum.inr 1)))
  bound:=Polynomial.C 8*Polynomial.X+Polynomial.C 5*p.bound+Polynomial.C 4
  runs a:=by
    obtain ⟨cp,hcp,hp⟩:=p.runs a
    have h1:=moveWord_runs (Sum.inr 0 : p.K ⊕ Fin 2) (Sum.inl p.input) (Sum.inr 1)
      (by simp) (by simp) (by simp) (ea a)
    have h2:=hp.relabel (leftEmbed p.K (Fin 2)) (fun _=>[])
    simp only [overlay_singleton] at h2
    have h3:=moveWord_runs (Sum.inl p.output : p.K ⊕ Fin 2) (Sum.inr 0) (Sum.inr 1)
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨(4*(eb (f a)).length+2)+cp+(4*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    have hl:=p.output_length_le a
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

/-- Reinterpret the domain, with its entire previous encoding still on tape. -/
def precompose (p : Procedure ea eb f) (h : γ→α) :
    Procedure (fun a=>ea (h a)) eb (fun a=>f (h a)) where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=p.runs (h a)

def congrEncoding (p : Procedure ea eb f) {ec : α→List Bool} {ed : β→List Bool}
    (ha : ∀a,ea a=ec a) (hb : ∀b,eb b=ed b) : Procedure ec ed f where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [ha,hb] using p.runs a

/-- Change the mathematical output only when its *actual encoded word* agrees. -/
def result (p : Procedure ea eb f) {ec : γ→List Bool} {h : α→γ}
    (hr : ∀a,eb (f a)=ec (h a)) : Procedure ea ec h where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [hr a] using p.runs a

noncomputable def unprefix (ea : α→List Bool) (b : Bool) :
    Procedure (fun a=>b::ea a) ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs a:=by
    refine ⟨2,by simp,?_⟩
    have hu : Function.update (singletonStore () (b::ea a)) () (ea a)=
        singletonStore () (ea a):=by simp [singletonStore]
    cases b
    · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
    · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def chooseBit (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (fun x : Bool×α=>x.1::ea x.2) eb (fun x=>if x.1 then g x.2 else f x.2) where
  K:=(p.K ⊕ q.K) ⊕ Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=Sum.inr 0
  output:=Sum.inr 0
  program:=.cases (Sum.inr 0) .skip
    (p.shared.program.relabel (leftPublic p.K q.K))
    (q.shared.program.relabel (rightPublic p.K q.K))
  bound:=p.shared.bound+q.shared.bound+1
  runs x:=by
    rcases x with ⟨b,a⟩
    have hpmono:=eval_nat_mono p.shared.bound (Nat.le_succ (ea a).length)
    have hqmono:=eval_nat_mono q.shared.bound (Nat.le_succ (ea a).length)
    cases b
    · obtain ⟨c,hc,hd⟩:=p.shared.runs a
      have hh:=hd.relabel (leftPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : leftPublic p.K q.K p.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hpmono).trans (Nat.le_add_right _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (false::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_false (p:=Program.skip)
          (r:=q.shared.program.relabel (rightPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (false::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)
    · obtain ⟨c,hc,hd⟩:=q.shared.runs a
      have hh:=hd.relabel (rightPublic p.K q.K) (fun _=>[])
      simp only [overlay_singleton] at hh
      have he : rightPublic p.K q.K q.shared.input=Sum.inr 0:=rfl
      rw [he] at hh
      refine ⟨c+1,?_,?_⟩
      · rw [Polynomial.eval_add,Polynomial.eval_add,Polynomial.eval_one]
        exact Nat.add_le_add_right ((hc.trans hqmono).trans (Nat.le_add_left _ _)) 1
      · have hu : Function.update (singletonStore (Sum.inr 0 : (p.K⊕q.K)⊕Fin 2)
            (true::ea a)) (Sum.inr 0) (ea a)=singletonStore (Sum.inr 0) (ea a):=by
          simp [singletonStore]
        simpa only [hu] using Runs.cases_true (p:=Program.skip)
          (q:=p.shared.program.relabel (leftPublic p.K q.K))
          (xs:=ea a) (s:=singletonStore (Sum.inr 0) (true::ea a)) (by simp [singletonStore])
          (by rw [hu];exact hh)

abbrev boolCode (b : Bool) : List Bool := [b]
noncomputable def choose (p : Procedure ea eb f) (q : Procedure ea eb g) :
    Procedure (prodCode boolCode ea) eb (fun x=>if x.1 then g x.2 else f x.2) := by
  let pp:=p.comp (unprefix ea false)
  let qq:=q.comp (unprefix ea false)
  exact ((chooseBit pp qq).comp
    (unprefix (fun x : Bool×α=>x.1::false::ea x.2) true)).congrEncoding
      (by intro x;rfl) (by intro b;rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
