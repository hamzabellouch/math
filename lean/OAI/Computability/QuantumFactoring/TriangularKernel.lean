import Mathlib
import OAI.Computability.QuantumFactoring.TriangularAlgebra
import OAI.Computability.QuantumFactoring.PhasePreparationConnection

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.Triangular
open scoped BigOperators
open OrderTrial

lemma phase_half (x : ℝ) : phase (x+1/2) = -phase x := by
  rw [show x+1/2 = (x+1/4)+1/4 by ring, phase_quarter, phase_quarter]
  simp only [neg_mul, mul_neg, neg_neg, ← mul_assoc, Complex.I_mul_I]
  ring

lemma phase_nat_half (x : ℝ) (h : ℕ) :
    phase (x+(h:ℝ)/2) = (-1:ℂ)^h*phase x := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [show x+((h+1:ℕ):ℝ)/2 = (x+(h:ℝ)/2)+1/2 by push_cast; ring,
      phase_half, ih, pow_succ]
    ring

lemma phase_product {b : ℕ} (hb : 1 ≤ b) (x y : Bits b) :
    phase ((inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b) =
      (-1:ℂ)^dot x y * phase ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b) := by
  have hq : (2:ℝ)^b ≠ 0 := by positivity
  have hh : 2*(2:ℝ)^(b-1) = (2:ℝ)^b := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hb]
  have hd := congrArg (Nat.cast : ℕ → ℝ) (product_decomposition x y)
  push_cast at hd
  have he : (inputNumber x : ℝ)*outputNumber y/(2:ℝ)^b =
      (∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2 +
        (∑ i, ∑ j, highTerm x y i j : ℕ) := by
    push_cast
    rw [hd]
    field_simp
    nlinarith [hh]
  rw [he]
  have hp := phase_add_int
    ((∑ i, ∑ j, lowTerm x y i j : ℕ)/(2:ℝ)^b + (dot x y : ℝ)/2)
    ((∑ i, ∑ j, highTerm x y i j : ℕ) : ℤ)
  simp only [Int.cast_natCast] at hp
  rw [hp, phase_nat_half]

noncomputable def residuePhase (a : ℕ) (z : ZMod (2^(a+2))) : ℂ :=
  phaseState (2^a) z.val

lemma residuePhase_correlation (a D : ℕ) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a (z+(D:ZMod (2^(a+2))))) *
      residuePhase a z) = phase ((D:ℝ)/(2:ℝ)^(a+2)) := by
  have hQ : 2^(a+2) = 4*2^a := by ring
  rw [← Equiv.sum_comp (ZMod.finEquiv (2^(a+2))).toEquiv]
  have hv {n : ℕ} [NeZero n] (z : Fin n) : ((ZMod.finEquiv n).toEquiv z).val = z.val := by
    cases n with
    | zero => exact False.elim (NeZero.ne 0 rfl)
    | succ n => rfl
  simp only [residuePhase, ZMod.val_add, ZMod.val_natCast,
    hv, Nat.add_mod_mod]
  change (∑ x : Fin (2^(a+2)), (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) x.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => star (phaseState (2^a)
    ((t+D) % 2^(a+2))) * phaseState (2^a) t) (2^(a+2)), hQ,
    phaseState_overlap (by positivity)]
  congr 1
  push_cast
  ring

/-- The full triangular coherent path expansion has exactly the manuscript's
selected kernel, after the phase register is tested in its prepared state. -/
theorem selected_kernel (a : ℕ) (x y : Bits (a+2)) :
    (∑ z : ZMod (2^(a+2)), star (residuePhase a z) *
      evolve (fun j v => (rowShift j v : ZMod (2^(a+2)))) x (residuePhase a)
        (a+2) le_rfl y z) =
      (Real.sqrt ((2:ℝ)^(a+2)) : ℂ)⁻¹ *
        phase ((inputNumber x:ℝ)*outputNumber y/(2:ℝ)^(a+2)) := by
  rw [selected_evolve, pathWeight_full, pathShift_rows,
    residuePhase_correlation, phase_product (by omega), hadamard_normalization]
  ring

end ExactQuantumFactoring.Triangular


end

end OAI
