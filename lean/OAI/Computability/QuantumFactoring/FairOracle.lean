import Mathlib
import OAI.Computability.QuantumFactoring.InitialOrderState
import OAI.Computability.QuantumFactoring.FactorGuess

namespace OAI

section
open scoped BigOperators


/-! Actual fair-bit initialization followed by clean reversible Boolean
computation.  All random bits remain in the returned physical state. -/
namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork Exactness

lemma outcomeMass_encode {α : Type*} [Fintype α] {q : ℕ}
    (e : α → Basis q) (he : Function.Injective e) (ψ : α → ℂ)
    (P : Basis q → Prop) :
    outcomeMass P (encodeState e ψ)=outcomeMass (P ∘ e) ψ := by
  classical
  unfold outcomeMass
  have hz : ∀ x ∈ (Finset.univ : Finset (Basis q)),
      x ∉ Finset.univ.image e →
      (if P x then Complex.normSq (encodeState e ψ x) else 0)=0 := by
    intro x _ hx
    have ho : x ∉ Set.range e := by
      rintro ⟨a,rfl⟩
      exact hx (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    rw [encodeState_outside e ψ x ho]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) hz,
    Finset.sum_image (fun _ _ _ _ h => he h)]
  simp only [encodeState_at e he,Function.comp_apply]

def fairOracle {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (hr : c.net.count ≤ r) :
    List (Instruction (n+b+m+r)) :=
  firstProgram m r (rightProgram n (hadamardPrefix b b le_rfl)) ++ oracleOn c hr

lemma fairOracle_length {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (hr : c.net.count ≤ r) :
    (fairOracle c hr).length ≤ b+4*c.net.count+2*m := by
  have h := oracleOn_length c hr
  simp only [fairOracle,List.length_append,firstProgram_length,rightProgram,List.length_map,
    hadamardPrefix_length]
  omega

lemma fairOracle_state {n b m r : ℕ} (c : BooleanNetwork (n+b) m)
    (hr : c.net.count ≤ r) (a : Basis n) :
    (programMatrix (fairOracle c hr)).mulVec
      (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false))) =
      encodeState (fun x => packed r (Fin.append a x) (c.eval (Fin.append a x))) (fairState b) := by
  rw [fairOracle,programMatrix_append,← Matrix.mulVec_mulVec,firstProgram_basis,
    rightProgram_basis,hadamards_zero,encodeState_comp]
  change (programMatrix (oracleOn c hr)).mulVec
    (encodeState (fun x => packed r (Fin.append a x) (fun _ => false)) (fairState b)) = _
  rw [encodeState,Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul,oracleOn_basis,Bool.false_xor]
  rfl

lemma fairOracle_embedding {n b m r : ℕ} (c : BooleanNetwork (n+b) m) (a : Basis n) :
    Function.Injective (fun x : Basis b => packed r (Fin.append a x) (c.eval (Fin.append a x))) := by
  intro x y h
  have hh := (packed_eq_iff _ _ _ _).mp h
  exact append_right_injective a hh.1

lemma fairOracle_mass {n b m r : ℕ} (c : BooleanNetwork (n+b) m)
    (hr : c.net.count ≤ r) (a : Basis n) (P : Basis (n+b+m+r) → Prop) [DecidablePred P] :
    outcomeMass P ((programMatrix (fairOracle c hr)).mulVec
      (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false)))) =
      (∑ x : Basis b, if P (packed r (Fin.append a x) (c.eval (Fin.append a x)))
        then (2:ℝ)⁻¹^b else 0) := by
  rw [fairOracle_state,outcomeMass_encode _ (fairOracle_embedding c a)]
  simp only [outcomeMass,Function.comp_apply,fairState_mass]

/-- A designated target bit of the packed clean oracle output. -/
def packedOutputBit {n m r : ℕ} (i : Fin m) (x : Basis (n+m+r)) : Bool :=
  x ((Fin.natAdd n i).castAdd r)

lemma packedOutputBit_eval {n m r : ℕ} (a : Basis n) (b : Basis m) (i : Fin m) :
    packedOutputBit (r:=r) i (packed r a b)=b i := by
  exact packed_target a b i

/-- The small, everywhere positive branch of Section 6, now with a physical
program and the concrete AKS verifier, not an abstract random-guess oracle. -/
lemma verified_guess_physical_mass {n r : ℕ} (hn : 128 ≤ n)
    (hr : (guessVerifier n).net.count ≤ r) (a : Basis n)
    (hN : 2 ≤ (bitsValue a).toNat) :
    outcomeMass (fun x => packedOutputBit (n:=n+n*n) (m:=1) (r:=r) 0 x=true)
      ((programMatrix (fairOracle (n:=n) (b:=n*n) (guessVerifier n) hr)).mulVec
        (basisVector (packed r (Fin.append a (fun _ => false)) (fun _ => false)))) =
      (2:ℝ)⁻¹^(n*n) := by
  rw [fairOracle_state,outcomeMass_encode _ (fairOracle_embedding (guessVerifier n) a)]
  change outcomeMass (fun x : Basis (n*n) =>
    packedOutputBit (r:=r) 0 (packed r (Fin.append a x) ((guessVerifier n).eval (Fin.append a x)))=true)
    (fairState (n*n)) = _
  simp_rw [packedOutputBit_eval,guessVerifier_correct hn]
  exact fair_guess_mass hN (bitsValue a).isLt

end ExactQuantumFactoring


end

end OAI
