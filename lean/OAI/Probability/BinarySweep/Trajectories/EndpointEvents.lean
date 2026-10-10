import Mathlib
import OAI.Probability.BinarySweep.FiniteLaws.UniformFiniteProbability

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
open Sparse

variable {b h : ℕ} {bits : Fin b → ℕ}

lemma gridLayer_at (g : GridChoices bits) (j : Fin b) (x : GridSlot bits) :
    gridLayer bits g j x j = g j (fun i => x i) (x j) := by
  simp [gridLayer,Equiv.piSplitAt_symm_apply]

@[simp] lemma independentPosition_zero (e : GridSlot bits × GridSlot bits) :
    independentPosition e 0=e.1 := by ext i; simp [independentPosition]

@[simp] lemma independentPosition_last (e : GridSlot bits × GridSlot bits) :
    independentPosition e (Fin.last b)=e.2 := by ext i; simp [independentPosition]

def endpointLine (e : GridSlot bits × GridSlot bits) (j : Fin b) : GridOutside bits j :=
  fun i => independentPosition e j.castSucc i

lemma endpoint_gridLayer_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) (j : Fin b) :
    gridLayer bits g j (independentPosition e j.castSucc)=independentPosition e j.succ ↔
      g j (endpointLine e j) (e.1 j)=e.2 j := by
  unfold endpointLine
  constructor
  · intro he
    have hh := congrFun he j
    simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
      Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using hh
  · intro he
    funext i
    by_cases hi : i=j
    · subst i
      simpa only [gridLayer_at,endpointLine,independentPosition,Fin.val_castSucc,
        Fin.val_succ,lt_self_iff_false,ite_false,Nat.lt_succ_self,ite_true] using he
    · rw [gridLayer_other bits g j i hi]
      exact (independentPosition_changes e j i hi).symm

lemma gridSweep_endpoint_iff (g : GridChoices bits) (e : GridSlot bits × GridSlot bits) :
    gridSweep bits g e.1=e.2 ↔ ∀j, g j (endpointLine e j) (e.1 j)=e.2 j := by
  constructor
  · intro he j
    have hp (t : Fin (b+1)) : gridPartialSweep bits g t e.1=independentPosition e t := by
      have hh := independentPosition_of_path (fun t => gridPartialSweep bits g t e.1)
        (gridPartialSweep_changes bits g e.1) t
      simpa only [gridPartialSweep_zero,Equiv.Perm.one_apply,gridPartialSweep_last,he] using hh.symm
    apply (endpoint_gridLayer_iff g e j).mp
    rw [← hp j.castSucc,← hp j.succ,gridPartialSweep_succ,Equiv.Perm.mul_apply]
  · intro he
    have hh := chronological_trajectory b (gridLayer bits g) (independentPosition e)
      (fun j => (endpoint_gridLayer_iff g e j).mpr (he j))
    simpa only [independentPosition_zero,independentPosition_last,gridSweep] using hh

variable {I : Type*} [Fintype I] [DecidableEq I]

def localEndpointEvent (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) : Prop :=
  ∀i ∈ A, endpointLine (e i) j=y → σ ((e i).1 j)=(e i).2 j

def endpointMass (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) : ℝ :=
  ∑g : GridChoices bits, if pathEvent H g ∧ ∀i ∈ A, gridSweep bits g (e i).1=(e i).2 then
    gridWeight bits z g else 0

def localEndpointMass (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) (j : Fin b) (y : GridOutside bits j) : ℝ :=
  ∑σ, if Assigns (lineInput H j y) (lineOutput H j y) σ ∧ localEndpointEvent A e j y σ then
    lineLaw (bits j) z σ else 0

lemma endpointMass_factor (H : PathFamily bits h) (z : ℝ) (A : Finset I)
    (e : I → GridSlot bits × GridSlot bits) :
    endpointMass H z A e = ∏j, ∏y, localEndpointMass H z A e j y := by
  have he (g : GridChoices bits) :
      (pathEvent H g ∧ ∀i ∈ A, gridSweep bits g (e i).1=(e i).2) ↔
      ∀j y, Assigns (lineInput H j y) (lineOutput H j y) (g j y) ∧
        localEndpointEvent A e j y (g j y) := by
    rw [pathEvent_iff_assigns]
    simp_rw [gridSweep_endpoint_iff]
    constructor
    · rintro ⟨hg,hp⟩ j y
      refine ⟨hg j y,?_⟩
      intro i hi hiy
      rw [← hiy]
      exact hp i hi j
    · intro hh
      refine ⟨fun j y => (hh j y).1,?_⟩
      intro i hi j
      exact (hh j (endpointLine (e i) j)).2 i hi rfl
  unfold endpointMass localEndpointMass
  rw [← sum_prod_grid]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Fintype.prod_ite_zero]
  simp only [he,gridWeight]
  split_ifs <;> rfl

omit [Fintype I] in
lemma localEndpointEvent_insert (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (i : I) (j : Fin b) (y : GridOutside bits j) (σ : Equiv.Perm (Slot (bits j))) :
    localEndpointEvent (insert i A) e j y σ ↔
      (endpointLine (e i) j=y → σ ((e i).1 j)=(e i).2 j) ∧ localEndpointEvent A e j y σ := by
  simp only [localEndpointEvent,Finset.mem_insert,forall_eq_or_imp]

omit [Fintype I] [DecidableEq I] in
lemma localEndpointEvent_empty_line (A : Finset I) (e : I → GridSlot bits × GridSlot bits)
    (j : Fin b) (y : GridOutside bits j) (ha : ∀i ∈ A, endpointLine (e i) j≠y)
    (σ : Equiv.Perm (Slot (bits j))) : localEndpointEvent A e j y σ := by
  intro i hi hiy
  exact (ha i hi hiy).elim

lemma assigns_empty_line (H : PathFamily bits h) (j : Fin b) (y : GridOutside bits j)
    (hn : ∀k, (fun i : {i : Fin b // i≠j} => H.position j.castSucc k i) ≠ y)
    (σ : Equiv.Perm (Slot (bits j))) : Assigns (lineInput H j y) (lineOutput H j y) σ := by
  intro k
  exact (hn k.val k.property).elim

end BinaryCoordinateSweeps

end

end OAI
