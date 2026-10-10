import Mathlib
import OAI.Computability.QuantumFactoring.TensorPreparation
import OAI.Computability.QuantumFactoring.CompletedOrderSlots

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open Exactness RepeatedTrials OrderTrial
namespace OrderSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (rawWidth n (sampleExponent n) n) (n^5)
abbrev coinWidth (n : ℕ) := Completion.coinBits (Completion.transitionWidth n) (2*n) ((n+10)*n^5)
abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+coinWidth n))

def ordinaryLayout (n : ℕ) : (Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n)≃Basis (ordinaryWidth n) :=
  (Equiv.piCongrRight (fun _ => rawLayout n (sampleExponent n) n)).trans
    (tensorLayout (rawWidth n (sampleExponent n) n) (n^5))
def layout (n : ℕ) : Result n≃Basis (width n) :=
  productLayout (Equiv.refl _) (productLayout (ordinaryLayout n)
    (productLayout (Equiv.refl _) (Equiv.refl _)))

def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))
    (Completion.transitionWidth n) (2*n) ((n+10)*n^5)

noncomputable def zero {n : ℕ} (a m : Basis n) : Result n :=
  ((fun _ => false),(fun _ => rawZero (sampleExponent n) n a m),(fun _ => false),(fun _ => false))

lemma ordinary_entry (n : ℕ) (a m : Basis n) (r : Fin (n^5)→OrderTrial.Raw n (sampleExponent n) n) :
    (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
      (basisVector (ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m)))
      (ordinaryLayout n r)=tensorState (rawState (sampleExponent n) n a m) (n^5) r := by
  change (programMatrix (tensorProgram (rawProgram n (sampleExponent n) n) (n^5))).mulVec
    (basisVector (tensorLayout _ _ (fun _ => rawLayout _ _ _ (rawZero _ _ a m))))
    (tensorLayout _ _ (fun i => rawLayout _ _ _ (r i)))=_
  rw [tensorProgram_entry]
  simp only [rawProgram_entry,tensorState]

/-- The completed order slot is a literal finite gate program on fresh qubits.
Neither the true order nor retrospective factor data occur in its preparation. -/
lemma program_entry (n : ℕ) (a m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero a m))) (layout n r)=fresh n a m r := by
  change (programMatrix (Completion.program _ _ _ _)).mulVec
    (basisVector (Completion.layout _ _ _ _
      ((fun _ => false),ordinaryLayout n (fun _ => rawZero (sampleExponent n) n a m),
        (fun _ => false),(fun _ => false))))
    (Completion.layout _ _ _ _ (r.1,ordinaryLayout n r.2.1,r.2.2))=_
  rw [Completion.program_entry]
  simp only [fresh,Completion.fresh,independentState]
  rw [ordinary_entry]

lemma program_state (n : ℕ) (a m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero a m)))=
      encodeState (layout n) (fresh n a m) := by
  funext x
  obtain ⟨r,rfl⟩ := (layout n).surjective x
  rw [program_entry,encodeState_at _ (layout n).injective]

lemma program_mass (n : ℕ) (a m : Basis n) (P : Result n→Prop) :
    outcomeMass (P ∘ (layout n).symm)
      ((programMatrix (program n)).mulVec (basisVector (layout n (zero a m))))=
      outcomeMass P (fresh n a m) := by
  rw [program_state,outcomeMass_encode _ (layout n).injective]
  congr 1
  funext r
  simp

lemma program_passed_mass {n : ℕ} (hn : 128 ≤ n) (a m : Basis n) (hm : 2 ≤ (bitsValue m).toNat) :
    outcomeMass (passed a m ∘ (layout n).symm)
      ((programMatrix (program n)).mulVec (basisVector (layout n (zero a m))))=(Completion.target n:ℝ) := by
  rw [program_mass]
  exact passed_mass hn a m hm

lemma program_length (n : ℕ) :
    (program n).length ≤ n^5*(2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n)+2*n+Completion.transitionWidth n+coinWidth n := by
  have hh := OrderSample.completeSampler_length n (sampleExponent n)
  have hr : (rawProgram n (sampleExponent n) n).length ≤
      2+((sampleExponent n+2)+4*OrderSample.scratch n (sampleExponent n+2)+
      2*n+(sampleExponent n+2)*(998*(sampleExponent n+2)+49)+2*(sampleExponent n+5))+
      3*n+retentionBits n := by
    simp only [rawProgram,parallelProgram_length,hadamardPrefix_length,guessProgram_length]
    omega
  unfold program
  rw [Completion.program_length,tensorProgram_length]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ hr) _) _) _

end OrderSlots
end ExactQuantumFactoring


end

end OAI
