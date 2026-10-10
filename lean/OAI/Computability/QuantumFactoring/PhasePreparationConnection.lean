import Mathlib
import OAI.Computability.QuantumFactoring.Exactness
import OAI.Computability.QuantumFactoring.BitEncoding
import OAI.Computability.QuantumFactoring.PhasePreparation

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators

lemma sqrt_two_pow (b : ℕ) : Real.sqrt ((2:ℝ)^b) = Real.sqrt 2 ^ b := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma hadamard_normalization (b : ℕ) :
    (Real.sqrt 2 : ℂ)⁻¹ ^ b = (Real.sqrt ((2:ℝ)^b) : ℂ)⁻¹ := by
  rw [sqrt_two_pow, Complex.ofReal_pow, inv_pow]

lemma preparePhase_label (b : ℕ) (y : Basis (b+2)) :
    (programMatrix (preparePhase (b+2) (by omega))).mulVec
        (basisVector (fun _ => false)) y =
      OrderTrial.phaseState (2^b) (bitsValue y).toNat := by
  rw [preparePhase_correct, hadamard_normalization]
  unfold OrderTrial.phaseState OrderTrial.phaseLabel
  rw [bitsValue_quarter]
  have he : (4:ℝ)*(2^b:ℕ) = (2:ℝ)^(b+2) := by push_cast; ring
  rw [he]
  have h₁ : (⟨b+2-1, by omega⟩ : Fin (b+2)) = Fin.last (b+1) := Fin.ext (by simp)
  have h₂ : (⟨b+2-2, by omega⟩ : Fin (b+2)) = (Fin.last b).castSucc := Fin.ext (by simp)
  rw [h₁, h₂]
  cases y (Fin.last (b+1)) <;> cases y (Fin.last b).castSucc <;>
    simp

/-- The physical wire basis is explicitly identified with the natural residue
labels; no implicit change in bit order is hidden in the overlap theorem. -/
def basisNumber (b : ℕ) : Basis b ≃ Fin (2^b) :=
  (bitsEquiv b).trans BitVec.equivFin.toEquiv

lemma basisNumber_val (b : ℕ) (x : Basis b) :
    (basisNumber b x).val = (bitsValue x).toNat := rfl

lemma basis_sum_range (b : ℕ) (f : ℕ → ℂ) :
    (∑ x : Basis b, f (bitsValue x).toNat) = ∑ i ∈ Finset.range (2^b), f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact (basisNumber b).sum_comp (fun i => f i.val)

noncomputable def preparedPhase (b : ℕ) : State (b+2) :=
  (programMatrix (preparePhase (b+2) (by omega))).mulVec (basisVector (fun _ => false))

lemma preparedPhase_overlap (b D : ℕ) :
    (∑ y : Basis (b+2),
      star (OrderTrial.phaseState (2^b) (((bitsValue y).toNat+D) % 2^(b+2))) *
        preparedPhase b y) = OrderTrial.phase ((D:ℝ)/(2:ℝ)^(b+2)) := by
  simp only [preparedPhase, preparePhase_label]
  rw [basis_sum_range (b+2) (fun v =>
    star (OrderTrial.phaseState (2^b) ((v+D)%2^(b+2))) * OrderTrial.phaseState (2^b) v)]
  have he : 2^(b+2) = 4*2^b := by ring
  rw [he, OrderTrial.phaseState_overlap (by positivity)]
  congr 1
  push_cast
  ring

end ExactQuantumFactoring


end

end OAI
