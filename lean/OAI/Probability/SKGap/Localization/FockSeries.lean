import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryGraph
import OAI.Probability.SKGap.Matrix.LoopPrediction

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram InverseDiagram WordSeries Loop
variable {ι : Type*}
abbrev Seq := ℕ→Space (ι:=ι)

def ofVector (v : Space (ι:=ι)) : Seq (ι:=ι) := fun n => if n=0 then v else 0

def shift : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun v n := match n with | 0 => 0 | n+1 => v n
  map_add' _ _ := by ext n i I; cases n <;> simp
  map_smul' _ _ := by ext n i I; cases n <;> simp

def act (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun v n := A (v n)
  map_add' _ _ := by funext n; exact A.map_add _ _
  map_smul' _ _ := by funext n; exact A.map_smul _ _

@[simp] lemma shift_zero (v : Seq (ι:=ι)) : shift v 0=0 := rfl
@[simp] lemma shift_succ (v : Seq (ι:=ι)) (n : ℕ) : shift v (n+1)=v n := rfl
@[simp] lemma act_apply (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Seq (ι:=ι)) (n : ℕ) :
    act A v n=A (v n) := rfl
lemma act_shift (A : Space (ι:=ι)→ₗ[ℝ] Space (ι:=ι)) (v : Seq (ι:=ι)) :
    act A (shift v)=shift (act A v) := by ext n; cases n <;> simp

variable [Fintype ι]

def inverseSeq (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) : Seq (ι:=ι)
  | 0 => v 0
  | 1 => v 1+diagonal a (noise j (v 0))
  | n+2 => v (n+2)+diagonal a (noise j (inverseSeq j a v (n+1)))-
      (j*Diagram.mean a) • diagonal a (inverseSeq j a v n)

lemma inverseSeq_add (j : ℝ) (a : ι→ℝ) (v w : Seq (ι:=ι)) :
    inverseSeq j a (v+w)=inverseSeq j a v+inverseSeq j a w := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp only [inverseSeq,Pi.add_apply,map_add]; abel
  | more n ih0 ih1 =>
    simp only [inverseSeq,Pi.add_apply] at ih0 ih1 ⊢
    rw [ih0,ih1]
    simp only [map_add,smul_add]
    abel
lemma inverseSeq_smul (j c : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverseSeq j a (c • v)=c • inverseSeq j a v := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [inverseSeq,map_smul,smul_add]
  | more n ih0 ih1 =>
    simp only [inverseSeq,Pi.smul_apply] at ih0 ih1 ⊢
    rw [ih0,ih1]
    simp only [map_smul,smul_add,smul_sub,smul_smul]
    rw [mul_comm (j*Diagram.mean a) c]

def inverse (j : ℝ) (a : ι→ℝ) : Seq (ι:=ι)→ₗ[ℝ] Seq (ι:=ι) where
  toFun := inverseSeq j a
  map_add' := inverseSeq_add j a
  map_smul' c v := inverseSeq_smul j c a v

lemma inverse_equation (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverse j a v=v+shift (act ((diagonal a).comp (noise j)) (inverse j a v))-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) (inverse j a v))) := by
  funext n
  rcases n with _|n
  · simp [inverse,inverseSeq]
  rcases n with _|n
  · simp [inverse,inverseSeq]
  · rfl

lemma inverse_unique (j : ℝ) (a : ι→ℝ) (v u : Seq (ι:=ι))
    (hu : u=v+shift (act ((diagonal a).comp (noise j)) u)-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) u))) :
    u=inverse j a v := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => have h:=congrFun hu 0; simpa [inverse,inverseSeq] using h
  | one =>
    have h0:=congrFun hu 0
    have h1:=congrFun hu 1
    simp only [Pi.add_apply,Pi.sub_apply,shift_zero,Pi.smul_apply,smul_zero,add_zero,sub_zero] at h0
    simpa [inverse,inverseSeq,h0] using h1
  | more n ih0 ih1 =>
    have h:=congrFun hu (n+2)
    simp only [Pi.add_apply,Pi.sub_apply,shift_succ,act_apply,LinearMap.comp_apply,Pi.smul_apply] at h
    rw [ih0,ih1] at h
    exact h

lemma inverse_shift (j : ℝ) (a : ι→ℝ) (v : Seq (ι:=ι)) :
    inverse j a (shift v)=shift (inverse j a v) := by
  symm
  apply inverse_unique
  have h:=congrArg shift (inverse_equation j a v)
  simpa only [map_add,map_sub,map_smul,act_shift] using h

lemma kernel_add_two_left (j : ℝ) (a : ι→ℝ) (n : ℕ) :
    kernel j a (n+2)=((diagonal a).comp (noise j)).comp (kernel j a (n+1))-
      (j*Diagram.mean a) • (diagonal a).comp (kernel j a n) := by
  have h := Fintype.sum_equiv (Equiv.ofBijective (blockPrepend n) (blockPrepend_bijective n))
    (fun s => match s with
      | .inl bs => word j (chain j a (true::bs.val))
      | .inr bs => word j (chain j a (false::bs.val)))
    (fun bs => word j (chain j a bs.val)) (by intro s; cases s <;> rfl)
  change _=kernel j a (n+2) at h
  rw [Fintype.sum_sum_type] at h
  rw [←h]
  simp only [chain_true,chain_false,word,letter,diagonal_scale,LinearMap.smul_comp]
  ext v i I
  simp [kernel,LinearMap.sum_apply,LinearMap.comp_apply,Finset.sum_neg_distrib,
    ←Finset.mul_sum,sub_eq_add_neg]

lemma inverse_ofVector (j : ℝ) (a : ι→ℝ) (v : Space (ι:=ι)) (n : ℕ) :
    inverse j a (ofVector v) n=kernel j a n v := by
  induction n using Nat.twoStepInduction with
  | zero => simp [inverse,inverseSeq,ofVector,kernel_zero]
  | one => simp [inverse,inverseSeq,ofVector,kernel_one]
  | more n ih0 ih1 =>
    change inverseSeq j a (ofVector v) (n+2)=_
    rw [inverseSeq]
    change ofVector v (n+2)+diagonal a (noise j (inverse j a (ofVector v) (n+1)))-
      (j*Diagram.mean a) • diagonal a (inverse j a (ofVector v) n)=_
    rw [ih0,ih1,kernel_add_two_left]
    simp [ofVector]

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.Noncrossing.Primary.Tensor.Series
open Diagram Loop
variable {ι : Type*} [Fintype ι]

def branchSource (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι)) : Seq (ι:=ι) :=
  act (diagonal p) U.2+V.1
def branchField (j : ℝ) (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι)) : Seq (ι:=ι) :=
  shift (act (noise j) (act (diagonal p) U.2))-
    (j*Diagram.mean p) • shift (shift U.1)+V.2

def ordinary (j : ℝ) : SourceTree (ι→ℝ)→Seq (ι:=ι)×Seq (ι:=ι)
  | .leaf c => (ofVector (c • vacuum),shift (ofVector (c • noise j vacuum)))
  | .branch p t u => (branchSource p (ordinary j t) (ordinary j u),
      branchField j p (ordinary j t) (ordinary j u))

lemma noise_vacuum (j : ℝ) : noise j (vacuum (ι:=ι))=creation vacuum := by
  rw [vacuum,←realize_noise]
  have h : Primary.noise j (Primary.vacuum (ι:=ι))=Primary.creation Primary.vacuum := by
    simp [Primary.noise,Primary.vacuum]
  rw [h,realize_creation]

lemma branch_field_creation (j : ℝ) (p : ι→ℝ) (U V : Seq (ι:=ι)×Seq (ι:=ι))
    (hU : U.2=shift (act creation U.1)) (hV : V.2=shift (act creation V.1)) :
    branchField j p U V=shift (act creation (branchSource p U V)) := by
  funext n
  cases n with
  | zero => simp [branchField,branchSource,hV]
  | succ n =>
    cases n with
    | zero => simp [branchField,branchSource,hU,hV]
    | succ n =>
      simp only [branchField,branchSource,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,
        hU,hV,shift_succ,act_apply,noise,LinearMap.add_apply,LinearMap.smul_apply,
        annihilation_diagonal_creation,map_add,smul_smul]
      abel

lemma ordinary_field_creation (j : ℝ) (t : SourceTree (ι→ℝ)) :
    (ordinary j t).2=shift (act creation (ordinary j t).1) := by
  induction t with
  | leaf c =>
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [ordinary,shift_succ,act_apply,ofVector]
      split_ifs <;> simp [noise_vacuum]
  | branch p t u ih1 ih2 => exact branch_field_creation j p _ _ ih1 ih2

def loopSource (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : Seq (ι:=ι) :=
  inverse j a (act (diagonal p) (ordinary j t).2-
    (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1)))
def loopField (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) : Seq (ι:=ι) :=
  shift (act (noise j) (loopSource j a p t))-
    (j*Diagram.mean a) • shift (shift (loopSource j a p t))-
    (j*Diagram.mean p) • shift (shift (ordinary j t).1)

lemma loop_source_equation (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopSource j a p t=act (diagonal a) (loopField j a p t)+
      act (diagonal p) (ordinary j t).2 := by
  have h := inverse_equation j a
    (act (diagonal p) (ordinary j t).2-
      (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1)))
  change loopSource j a p t =
    act (diagonal p) (ordinary j t).2-
      (j*Diagram.mean p) • shift (shift (act (diagonal a) (ordinary j t).1))+
      shift (act ((diagonal a).comp (noise j)) (loopSource j a p t))-
      (j*Diagram.mean a) • shift (shift (act (diagonal a) (loopSource j a p t))) at h
  refine h.trans ?_
  change _=act (diagonal a) (shift (act (noise j) (loopSource j a p t))-
    (j*Diagram.mean a) • shift (shift (loopSource j a p t))-
    (j*Diagram.mean p) • shift (shift (ordinary j t).1))+
      act (diagonal p) (ordinary j t).2
  simp only [map_sub,map_smul,act_shift]
  have hc : act ((diagonal a).comp (noise j)) (loopSource j a p t)=
      act (diagonal a) (act (noise j) (loopSource j a p t)) := rfl
  rw [hc]
  abel

lemma loop_source_zero (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopSource j a p t 0=0 := by
  have h:=congrFun (loop_source_equation j a p t) 0
  simpa [loopField,ordinary_field_creation j t] using h

theorem loop_field_creation (j : ℝ) (a p : ι→ℝ) (t : SourceTree (ι→ℝ)) :
    loopField j a p t=shift (act creation (loopSource j a p t)) := by
  have ht := ordinary_field_creation j t
  have hs := loop_source_equation j a p t
  have h (n : ℕ) : loopField j a p t (n+1)=creation (loopSource j a p t n) := by
    induction n with
    | zero => simp [loopField,loop_source_zero]
    | succ n ih =>
      have he := congrFun hs (n+1)
      simp only [Pi.add_apply,act_apply,ih,ht,shift_succ] at he
      change _ = creation (loopSource j a p t (n+1))
      simp only [loopField,Pi.sub_apply,Pi.smul_apply,shift_succ,act_apply]
      rw [noise,LinearMap.add_apply,LinearMap.smul_apply,he]
      simp only [map_add,annihilation_diagonal_creation,smul_add,smul_smul]
      abel
  funext n
  cases n with
  | zero => simp [loopField]
  | succ n => exact h n

inductive ClosedTree (D : Type*) where
  | leaf : ℝ→ClosedTree D
  | implicit : D→SourceTree D→ClosedTree D
  | branch : D→ClosedTree D→ClosedTree D→ClosedTree D

def ClosedTree.series (j : ℝ) (a : ι→ℝ) : ClosedTree (ι→ℝ)→Seq (ι:=ι)×Seq (ι:=ι)
  | .leaf c => ordinary j (.leaf c)
  | .implicit p t => (loopSource j a p t,loopField j a p t)
  | .branch p t u => (branchSource p (t.series j a) (u.series j a),
      branchField j p (t.series j a) (u.series j a))

def ClosedTree.leafMass {D : Type*} : ClosedTree D→ℝ
  | .leaf c => c
  | .implicit _ _ => 0
  | .branch _ _ u => u.leafMass

theorem ClosedTree.field_creation (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) :
    (t.series j a).2=shift (act creation (t.series j a).1) := by
  induction t with
  | leaf c => exact ordinary_field_creation j (.leaf c)
  | implicit p t => exact loop_field_creation j a p t
  | branch p t u ih1 ih2 => exact branch_field_creation j p _ _ ih1 ih2

theorem ClosedTree.project_field (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (n : ℕ) :
    project ((t.series j a).2 n)=0 := by
  rw [t.field_creation]
  cases n with
  | zero => simp
  | succ n => simp [project_creation]

theorem ClosedTree.project_source (j : ℝ) (a : ι→ℝ) (t : ClosedTree (ι→ℝ)) (n : ℕ) :
    project ((t.series j a).1 n)=if n=0 then (fun _ : ι => t.leafMass) else 0 := by
  induction t with
  | leaf c =>
    simp only [series,ordinary,ofVector,leafMass]
    split_ifs <;> simp [vacuum,project_realize,Primary.vacuum]
    ext index
    simp
  | implicit p t =>
    simp only [series,leafMass]
    simp only [Pi.zero_def,ite_self]
    rw [loop_source_equation,Pi.add_apply,act_apply,act_apply,
      loop_field_creation,ordinary_field_creation]
    cases n with
    | zero => simp; rfl
    | succ n => simp [project_diagonal_creation]; rfl
  | branch p t u ih1 ih2 =>
    simp only [series,branchSource,Pi.add_apply,act_apply,leafMass]
    rw [t.field_creation]
    cases n with
    | zero => simpa using ih2
    | succ n => simpa [project_diagonal_creation] using ih2

end SKGap.Noncrossing.Primary.Tensor.Series

end
end

end OAI
