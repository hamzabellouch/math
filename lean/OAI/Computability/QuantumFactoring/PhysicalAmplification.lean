import Mathlib
import OAI.Computability.QuantumFactoring.PackedPrograms
import OAI.Computability.QuantumFactoring.PhaseOracle

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

/-- A support invariant for a read-only classical input sector. -/
def Supported {ι : Type*} (S : ι → Prop) (v : ι → ℂ) : Prop :=
  ∀ x, ¬ S x → v x = 0

/-- Matrix entries cannot change the read-only input. -/
def RespectsSector {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ) : Prop :=
  ∀ x y, ¬ (S x ↔ S y) → U x y = 0

lemma RespectsSector.adjoint {ι : Type*} (S : ι → Prop) (U : Matrix ι ι ℂ)
    (h : RespectsSector S U) : RespectsSector S U.conjTranspose := by
  intro x y hxy
  change star (U y x) = 0
  rw [h y x (fun hyx => hxy hyx.symm),star_zero]

lemma RespectsSector.supported {ι : Type*} [Fintype ι] (S : ι → Prop)
    (U : Matrix ι ι ℂ) (h : RespectsSector S U) (v : ι → ℂ)
    (hv : Supported S v) : Supported S (U.mulVec v) := by
  classical
  intro x hx
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : S y
  · exact mul_eq_zero.mpr (Or.inl (h x y (by tauto)))
  · rw [hv y hy,mul_zero]

noncomputable def signState {ι : Type*} (p : ι → Bool) (v : ι → ℂ) : ι → ℂ :=
  fun x => (if p x then (-1:ℂ) else 1)*v x

lemma signState_supported {ι : Type*} (S : ι → Prop) (p : ι → Bool)
    (v : ι → ℂ) (hv : Supported S v) : Supported S (signState p v) := by
  intro x hx
  simp only [signState,hv x hx,mul_zero]

lemma signState_eq {ι : Type*} (p : ι → Bool) (v : ι → ℂ) :
    signState p v = fun x => v x-2*goodPart (fun y => p y=true) v x := by
  classical
  funext x
  simp only [signState,goodPart]
  split_ifs <;> ring

lemma sector_zero_sign {ι : Type*} [DecidableEq ι] (S : ι → Prop)
    (z : ι) (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    signState p v = v - ((2*v z) • basisVector z) := by
  classical
  funext x
  simp only [signState,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,basisVector]
  by_cases hx : S x
  · by_cases he : x=z
    · subst x
      simp [hp z hx]
      ring
    · simp [he, show p x ≠ true from fun h => he ((hp x hx).mp h)]
  · have hvx := hv x hx
    by_cases he : x=z
    · subst x
      simp [hvx]
    · simp [he,hvx]

lemma adjoint_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (z : ι) (v : ι → ℂ) :
    U.conjTranspose.mulVec v z = finiteInner (U.mulVec (basisVector z)) v := by
  rw [matrix_basisVector]
  rfl

/-- The physical sign on zero work, conjugated by a reversible preparation,
is minus the reflection about its output, within the invariant input fiber. -/
lemma conjugated_zero_sign {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hu : U ∈ Matrix.unitaryGroup ι ℂ)
    (S : ι → Prop) (hS : RespectsSector S U) (z : ι)
    (p : ι → Bool) (hp : ∀ x, S x → (p x=true ↔ x=z))
    (v : ι → ℂ) (hv : Supported S v) :
    U.mulVec (signState p (U.conjTranspose.mulVec v)) =
      -stateReflection (U.mulVec (basisVector z)) v := by
  rw [sector_zero_sign S z p hp _
    ((hS.adjoint S U).supported S U.conjTranspose _ hv)]
  have huu : U * U.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
    huu,Matrix.one_mulVec,adjoint_coordinate]
  funext x
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,stateReflection]
  ring

/-- Five actual programs: prepare, mark good, unprepare, mark zero work,
prepare. The two phase predicates share a clean flag and scratch area. -/
def amplificationProgram {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    List (Instruction (n+1+r)) :=
  firstProgram 1 r ops ++ phaseOracle good hg ++
    firstProgram 1 r (ops.reverse.map Instruction.reverse) ++ phaseOracle zero hz ++
      firstProgram 1 r ops

lemma amplificationProgram_length {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r) :
    (amplificationProgram ops good zero hg hz).length ≤
      3*ops.length+8*good.net.count+8*zero.net.count+12 := by
  have h₁ := phaseOracle_length good hg
  have h₂ := phaseOracle_length zero hz
  simp only [amplificationProgram,List.length_append,firstProgram_length,
    List.length_map,List.length_reverse]
  omega

lemma amplificationProgram_state {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (z : Basis n) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
    encodeState (fun x => packed r x (fun _ : Fin 1 => false))
      ((programMatrix ops).mulVec (signState (fun x => zero.eval x 0)
        ((programMatrix ops).conjTranspose.mulVec
          (signState (fun x => good.eval x 0)
            ((programMatrix ops).mulVec (basisVector z)))))) := by
  rw [amplificationProgram]
  simp only [programMatrix_append,← Matrix.mulVec_mulVec]
  rw [firstProgram_basis,phaseOracle_state,firstProgram_state,programMatrix_reverse]
  rw [phaseOracle_state,firstProgram_state]
  rfl

/-- Exact amplitude amplification implemented over the fixed named gates.
The semantic premises are preparation mass and the unchanged-input invariant,
not a gate oracle or an assumed reflection. -/
theorem physical_quarter_amplification {n r : ℕ} (ops : List (Instruction n))
    (good zero : BooleanNetwork n 1) (hg : good.net.count ≤ r) (hz : zero.net.count ≤ r)
    (S : Basis n → Prop) (hS : RespectsSector S (programMatrix ops))
    (z : Basis n) (hstart : S z)
    (hzero : ∀ x, S x → (zero.eval x 0=true ↔ x=z))
    (hquarter : outcomeMass (fun x => good.eval x 0=true)
      ((programMatrix ops).mulVec (basisVector z)) = 1/4) :
    (programMatrix (amplificationProgram ops good zero hg hz)).mulVec
      (basisVector (packed r z (fun _ : Fin 1 => false))) =
      encodeState (fun x => packed r x (fun _ : Fin 1 => false))
        (fun x => -2*goodPart (fun y => good.eval y 0=true)
          ((programMatrix ops).mulVec (basisVector z)) x) := by
  classical
  have hs : Supported S (basisVector z) := by
    intro x hx
    simp [basisVector,show x ≠ z from fun h => hx (h ▸ hstart)]
  have hv := hS.supported S (programMatrix ops) (basisVector z) hs
  have hn : (∑ x, Complex.normSq ((programMatrix ops).mulVec (basisVector z) x)) = 1 := by
    rw [unitary_mass _ (programMatrix_unitary ops)]
    simp [basisVector]
  rw [amplificationProgram_state,
    conjugated_zero_sign _ (programMatrix_unitary ops) S hS z _ hzero _
      (signState_supported S _ _ hv),signState_eq,
    one_reflection _ _ hn hquarter]
  congr 1
  funext x
  simp only [Pi.neg_apply]
  ring

end ExactQuantumFactoring


end

end OAI
