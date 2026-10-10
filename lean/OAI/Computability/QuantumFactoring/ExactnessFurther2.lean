import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalAmplification
import OAI.Computability.QuantumFactoring.ReadOnlyCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
namespace ExactQuantumFactoring
open scoped BigOperators

namespace Exactness

lemma RespectsSector.one {ι : Type*} [DecidableEq ι] (S : ι→Prop) :
    RespectsSector S (1 : Matrix ι ι ℂ) := by
  intro x y h
  have hxy : x≠y := fun he => h (he ▸ Iff.rfl)
  simp [hxy]

lemma RespectsSector.mul {ι : Type*} [Fintype ι] (S : ι→Prop)
    (U V : Matrix ι ι ℂ) (hU : RespectsSector S U) (hV : RespectsSector S V) :
    RespectsSector S (U*V) := by
  classical
  intro x y hxy
  apply Finset.sum_eq_zero
  intro z _
  change U x z*V z y=0
  by_cases hxz : S x↔S z
  · rw [hV z y (fun hzy => hxy (hxz.trans hzy)),mul_zero]
  · rw [hU x z hxz,zero_mul]

end Exactness
open Exactness

/-- A syntactic read-only rule suffices; no hypothesis about the state prepared
by the algorithm or its unknown factors occurs here. -/
def ReadOnly {q : ℕ} (inputs : Finset (Fin q)) (P : List (Instruction q)) : Prop :=
  ∀ o∈P,o.target∉inputs

def inputSector {q : ℕ} (inputs : Finset (Fin q)) (z x : Basis q) : Prop :=
  ∀ i∈inputs,x i=z i

lemma Instruction.respects_input {q : ℕ} (o : Instruction q) (inputs : Finset (Fin q))
    (ht : o.target∉inputs) (z : Basis q) : RespectsSector (inputSector inputs z) o.matrix := by
  intro x y hxy
  by_contra hne
  apply hxy
  have he (i : Fin q) (hi : i∈inputs) : x i=y i :=
    o.nonzero_eq x y hne i (fun h => ht (h ▸ hi))
  constructor
  · intro hx i hi
    rw [←he i hi]
    exact hx i hi
  · intro hy i hi
    rw [he i hi]
    exact hy i hi

lemma program_respects_input {q : ℕ} (inputs : Finset (Fin q))
    (P : List (Instruction q)) (hP : ReadOnly inputs P) (z : Basis q) :
    RespectsSector (inputSector inputs z) (programMatrix P) := by
  induction P with
  | nil => exact RespectsSector.one _
  | cons o P ih =>
    rw [programMatrix_cons]
    exact RespectsSector.mul _ _ _
      (ih (fun p hp => hP p (by simp [hp])))
      (o.respects_input inputs (hP o (by simp)) z)

end ExactQuantumFactoring


end

end OAI
