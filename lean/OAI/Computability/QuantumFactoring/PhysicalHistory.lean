import Mathlib
import OAI.Computability.QuantumFactoring.FairOracle
import OAI.Computability.QuantumFactoring.ParallelPreparation
import OAI.Computability.QuantumFactoring.ExactnessFurther2

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness

/-- Every previously retained bit, not merely the original N, is read-only for
an appended fresh transition. The transition may use them as controls. -/
def prefixWires (p q : ℕ) : Finset (Fin (p+q)) := Finset.univ.filter (fun i => i.val<p)

lemma append_prefix_sector {p q : ℕ} (h h' : Basis p) (z y : Basis q) :
    inputSector (prefixWires p q) (Fin.append h z) (Fin.append h' y) ↔ h'=h := by
  constructor
  · intro hs
    funext i
    have hh := hs (Fin.castAdd q i) (by simp [prefixWires])
    simpa only [Fin.append_left] using hh
  · rintro rfl i hi
    have hip : i.val<p := (Finset.mem_filter.mp hi).2
    let j : Fin p := ⟨i.val,hip⟩
    have hj : Fin.castAdd q j=i := Fin.ext rfl
    rw [←hj]
    simp only [Fin.append_left]

noncomputable def freshColumn {p q : ℕ} (P : List (Instruction (p+q))) (z : Basis q)
    (h : Basis p) (y : Basis q) : ℂ :=
  (programMatrix P).mulVec (basisVector (Fin.append h z)) (Fin.append h y)

/-- Actual gate program, sector by sector. All unused/tail amplitudes are kept:
this is not a normalized conditional state or a measurement hypothesis. -/
theorem retained_column {p q : ℕ} (P : List (Instruction (p+q)))
    (hP : ReadOnly (prefixWires p q) P) (h : Basis p) (z : Basis q) :
    (programMatrix P).mulVec (basisVector (Fin.append h z))=
      encodeState (fun y => Fin.append h y) (freshColumn P z h) := by
  classical
  funext x
  obtain ⟨⟨h',y⟩,rfl⟩ := (appendEquiv p q).surjective x
  change (programMatrix P).mulVec (basisVector (Fin.append h z)) (Fin.append h' y)=
    encodeState (fun y => Fin.append h y) (freshColumn P z h) (Fin.append h' y)
  by_cases he : h'=h
  · subst h'
    rw [encodeState_at _ (append_right_injective h)]
    rfl
  · have hs : Supported (inputSector (prefixWires p q) (Fin.append h z))
        (basisVector (Fin.append h z)) := by
      intro x hx
      have hxne : x≠Fin.append h z := by
        rintro rfl
        exact hx (fun _ _ => rfl)
      simp [basisVector,hxne]
    have hz := (program_respects_input (prefixWires p q) P hP (Fin.append h z)).supported
      _ _ _ hs (Fin.append h' y) (fun hh => he ((append_prefix_sector h h' z y).mp hh))
    rw [hz,encodeState_outside]
    rintro ⟨v,hv⟩
    have hh : (h,v)=(h',y) := (appendEquiv p q).injective hv
    exact he (congrArg Prod.fst hh).symm

/-- Coherent retained-work lemma used at every adaptive slot. A single actual
fixed-gate P acts correctly on an arbitrary (possibly entangled) old history. -/
theorem retained_step {p q : ℕ} (P : List (Instruction (p+q)))
    (hP : ReadOnly (prefixWires p q) P) (z : Basis q) (ψ : Basis p→ℂ) :
    (programMatrix P).mulVec (encodeState (fun h => Fin.append h z) ψ)=
      encodeState (appendEquiv p q) (RecordedHistory.appendState ψ (freshColumn P z)) := by
  rw [encodeState,Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul,retained_column P hP]
  unfold encodeState RecordedHistory.appendState
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_smul]
  rfl

/-- Each fresh column is normalized automatically by the verified unitary gate
semantics, even when no local transition succeeds. -/
theorem freshColumn_normalized {p q : ℕ} (P : List (Instruction (p+q)))
    (hP : ReadOnly (prefixWires p q) P) (z : Basis q) (h : Basis p) :
    ∑ y,Complex.normSq (freshColumn P z h y)=1 := by
  have hn := basis_preparation_normalized P (Fin.append h z)
  rw [retained_column P hP] at hn
  have hm := outcomeMass_encode (fun y : Basis q => Fin.append h y)
    (append_right_injective h) (freshColumn P z h) (fun _ => True)
  simp only [outcomeMass,Function.comp_apply,ite_true] at hm
  rw [←hm]
  exact hn

/-- Constant passing mass for an actual read-only physical transition on an
arbitrary superposition of retained histories. The test is on the same output
registers; no collapse or conditional renormalization is used. -/
theorem retained_constant_mass {p q : ℕ} (P : List (Instruction (p+q)))
    (hP : ReadOnly (prefixWires p q) P) (z : Basis q) (ψ : Basis p→ℂ)
    (passed : Basis p→Prop) (pass : Basis p→Basis q→Prop) (a : ℝ)
    (hlocal : ∀ h, passed h → outcomeMass (pass h) (freshColumn P z h)=a) :
    outcomeMass (fun x => let hy := (appendEquiv p q).symm x
        passed hy.1 ∧ pass hy.1 hy.2)
      ((programMatrix P).mulVec (encodeState (fun h => Fin.append h z) ψ)) =
      outcomeMass passed ψ*a := by
  classical
  rw [retained_step P hP]
  rw [outcomeMass_encode _ (appendEquiv p q).injective]
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using
    RecordedHistory.append_constant_mass ψ (freshColumn P z) passed pass a hlocal

end ExactQuantumFactoring


end

end OAI
