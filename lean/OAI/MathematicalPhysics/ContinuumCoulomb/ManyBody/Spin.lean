import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The two-spin Heisenberg interaction

The basis order is `↑↑, ↑↓, ↓↑, ↓↓`.  The matrix below is
`X ⊗ X + Y ⊗ Y + Z ⊗ Z = 2 SWAP - I` in that basis.
The exact singlet/triplet computation supplies the interaction bound
used when rounding or deleting source coefficients in both continuum
Coulomb manuscripts (their sections on rational source normalization).
-/

namespace ContinuumCoulomb

open Matrix Complex
open scoped BigOperators

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Tensor product written in the fixed four-state computational basis. -/
def twoSpinTensor (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  !![A 0 0 * B 0 0, A 0 0 * B 0 1, A 0 1 * B 0 0, A 0 1 * B 0 1;
     A 0 0 * B 1 0, A 0 0 * B 1 1, A 0 1 * B 1 0, A 0 1 * B 1 1;
     A 1 0 * B 0 0, A 1 0 * B 0 1, A 1 1 * B 0 0, A 1 1 * B 0 1;
     A 1 0 * B 1 0, A 1 0 * B 1 1, A 1 1 * B 1 0, A 1 1 * B 1 1]

/-- The spin-`1/2` isotropic Heisenberg matrix in the computational basis. -/
def heisenberg : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, -1, 2, 0;
     0, 2, -1, 0;
     0, 0, 0, 1]

theorem heisenberg_eq_pauli :
    heisenberg = twoSpinTensor pauliX pauliX +
      twoSpinTensor pauliY pauliY + twoSpinTensor pauliZ pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, twoSpinTensor, pauliX, pauliY, pauliZ]

/-- Exchange of the two spin coordinates in the computational basis. -/
def twoSpinSwap : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]

theorem heisenberg_eq_two_swap_sub_one :
    heisenberg = (2 : ℂ) • twoSpinSwap - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, twoSpinSwap, Matrix.one_apply]

theorem heisenberg_mulVec (u : Fin 4 → ℂ) :
    heisenberg *ᵥ u = ![u 0, -(u 1) + 2 * u 2, 2 * u 1 - u 2, u 3] := by
  ext i
  fin_cases i <;> simp [heisenberg, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

/-- The unnormalized singlet, of squared norm two. -/
def spinSinglet : Fin 4 → ℂ := ![0, 1, -1, 0]

def spinTripletUp : Fin 4 → ℂ := ![1, 0, 0, 0]

/-- The unnormalized zero-magnetization triplet, of squared norm two. -/
def spinTripletZero : Fin 4 → ℂ := ![0, 1, 1, 0]

def spinTripletDown : Fin 4 → ℂ := ![0, 0, 0, 1]

theorem heisenberg_singlet :
    heisenberg *ᵥ spinSinglet = (-3 : ℂ) • spinSinglet := by
  rw [heisenberg_mulVec]
  ext i
  fin_cases i <;> norm_num [spinSinglet]

theorem heisenberg_triplet_up :
    heisenberg *ᵥ spinTripletUp = spinTripletUp := by
  rw [heisenberg_mulVec]
  ext i
  fin_cases i <;> norm_num [spinTripletUp]

theorem heisenberg_triplet_zero :
    heisenberg *ᵥ spinTripletZero = spinTripletZero := by
  rw [heisenberg_mulVec]
  ext i
  fin_cases i <;> norm_num [spinTripletZero]

theorem heisenberg_triplet_down :
    heisenberg *ᵥ spinTripletDown = spinTripletDown := by
  rw [heisenberg_mulVec]
  ext i
  fin_cases i <;> norm_num [spinTripletDown]

/-- Every spin vector decomposes explicitly into its singlet and triplets. -/
theorem spin_singlet_triplet_decomposition (u : Fin 4 → ℂ) :
    u = u 0 • spinTripletUp + ((u 1 + u 2) / 2) • spinTripletZero +
      ((u 1 - u 2) / 2) • spinSinglet + u 3 • spinTripletDown := by
  ext i
  fin_cases i <;>
    simp [spinTripletUp, spinTripletZero, spinSinglet, spinTripletDown]
  <;> ring

def twoSpinNormSq (u : Fin 4 → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

def twoSpinEnergy (u : Fin 4 → ℂ) : ℝ :=
  (∑ i, star (u i) * (heisenberg *ᵥ u) i).re

theorem twoSpinNormSq_nonneg (u : Fin 4 → ℂ) : 0 ≤ twoSpinNormSq u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The upper form bound follows from the antisymmetric component. -/
theorem twoSpinEnergy_upper_identity (u : Fin 4 → ℂ) :
    twoSpinNormSq u - twoSpinEnergy u = 2 * Complex.normSq (u 1 - u 2) := by
  simp [twoSpinNormSq, twoSpinEnergy, heisenberg_mulVec,
    Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  ring

/-- The lower form bound follows from the symmetric components. -/
theorem twoSpinEnergy_lower_identity (u : Fin 4 → ℂ) :
    twoSpinEnergy u + 3 * twoSpinNormSq u =
      4 * Complex.normSq (u 0) + 2 * Complex.normSq (u 1 + u 2) +
        4 * Complex.normSq (u 3) := by
  simp [twoSpinNormSq, twoSpinEnergy, heisenberg_mulVec,
    Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  ring

theorem twoSpinEnergy_le (u : Fin 4 → ℂ) :
    twoSpinEnergy u ≤ twoSpinNormSq u := by
  have h := twoSpinEnergy_upper_identity u
  have hs := Complex.normSq_nonneg (u 1 - u 2)
  linarith

theorem twoSpinEnergy_ge (u : Fin 4 → ℂ) :
    -3 * twoSpinNormSq u ≤ twoSpinEnergy u := by
  have h := twoSpinEnergy_lower_identity u
  have h0 := Complex.normSq_nonneg (u 0)
  have h1 := Complex.normSq_nonneg (u 1 + u 2)
  have h3 := Complex.normSq_nonneg (u 3)
  linarith

/-- The interaction quadratic form has absolute value at most three
times the squared norm.  The singlet attains the lower endpoint. -/
theorem twoSpinEnergy_abs_le (u : Fin 4 → ℂ) :
    |twoSpinEnergy u| ≤ 3 * twoSpinNormSq u := by
  apply abs_le.mpr
  constructor
  · simpa using twoSpinEnergy_ge u
  · have hu := twoSpinEnergy_le u
    have hn := twoSpinNormSq_nonneg u
    linarith

theorem spinSinglet_normSq : twoSpinNormSq spinSinglet = 2 := by
  norm_num [twoSpinNormSq, spinSinglet, Fin.sum_univ_succ]

theorem spinSinglet_energy : twoSpinEnergy spinSinglet = -6 := by
  norm_num [twoSpinEnergy, heisenberg_mulVec, spinSinglet, Fin.sum_univ_succ]

/-- The coefficient-rounding estimate on a normalized two-spin state. -/
theorem heisenberg_coefficient_error
    (J K : ℝ) (u : Fin 4 → ℂ) (hu : twoSpinNormSq u = 1) :
    |J * twoSpinEnergy u - K * twoSpinEnergy u| ≤ 3 * |J - K| := by
  have h := twoSpinEnergy_abs_le u
  rw [hu, mul_one] at h
  calc
    |J * twoSpinEnergy u - K * twoSpinEnergy u| =
        |J - K| * |twoSpinEnergy u| := by rw [← sub_mul, abs_mul]
    _ ≤ |J - K| * 3 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 3 * |J - K| := mul_comm _ _

/-- A two-spin interaction tensored with any finite spectator space has
the same form bound.  The vector can be entangled with the spectators. -/
theorem heisenberg_spectator_form_bound
    {ι : Type*} [Fintype ι] (u : ι → Fin 4 → ℂ) :
    |∑ k, twoSpinEnergy (u k)| ≤ 3 * ∑ k, twoSpinNormSq (u k) := by
  calc
    |∑ k, twoSpinEnergy (u k)| ≤ ∑ k, |twoSpinEnergy (u k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, 3 * twoSpinNormSq (u k) :=
      Finset.sum_le_sum fun k _ => twoSpinEnergy_abs_le (u k)
    _ = 3 * ∑ k, twoSpinNormSq (u k) := (Finset.mul_sum _ _ _).symm

/-- The coefficient-rounding bound remains valid on a normalized state
with arbitrary entanglement with the remaining spins. -/
theorem heisenberg_spectator_coefficient_error
    {ι : Type*} [Fintype ι] (J K : ℝ) (u : ι → Fin 4 → ℂ)
    (hu : ∑ k, twoSpinNormSq (u k) = 1) :
    |J * (∑ k, twoSpinEnergy (u k)) - K * (∑ k, twoSpinEnergy (u k))| ≤
      3 * |J - K| := by
  have h := heisenberg_spectator_form_bound u
  rw [hu, mul_one] at h
  calc
    |J * (∑ k, twoSpinEnergy (u k)) - K * (∑ k, twoSpinEnergy (u k))| =
        |J - K| * |∑ k, twoSpinEnergy (u k)| := by rw [← sub_mul, abs_mul]
    _ ≤ |J - K| * 3 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 3 * |J - K| := mul_comm _ _

/-- Sum of coefficient errors for all source edges.  For each edge, `u e`
is the common state reindexed into its two interacting spins and all
spectators.  No product-state assumption is made. -/
theorem heisenberg_edge_rounding
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (J K : κ → ℝ) (u : κ → ι → Fin 4 → ℂ)
    (hu : ∀ e, ∑ k, twoSpinNormSq (u e k) = 1) :
    |∑ e, (J e - K e) * (∑ k, twoSpinEnergy (u e k))| ≤
      3 * ∑ e, |J e - K e| := by
  calc
    |∑ e, (J e - K e) * (∑ k, twoSpinEnergy (u e k))| ≤
        ∑ e, |(J e - K e) * (∑ k, twoSpinEnergy (u e k))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, 3 * |J e - K e| := by
      apply Finset.sum_le_sum
      intro e _
      simpa only [sub_mul] using
        heisenberg_spectator_coefficient_error (J e) (K e) (u e) (hu e)
    _ = 3 * ∑ e, |J e - K e| := (Finset.mul_sum _ _ _).symm

/-- The manuscripts' per-edge rounding budget gives total form error `3ε`. -/
theorem heisenberg_source_rounding
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (J K : κ → ℝ) (u : κ → ι → Fin 4 → ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hu : ∀ e, ∑ k, twoSpinNormSq (u e k) = 1)
    (hcoeff : ∀ e, |J e - K e| ≤ ε / (max 1 (Fintype.card κ) : ℕ)) :
    |∑ e, (J e - K e) * (∑ k, twoSpinEnergy (u e k))| ≤ 3 * ε := by
  have hsum : (∑ e, |J e - K e|) ≤ ε := by
    by_cases hcard : Fintype.card κ = 0
    · have hempty : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcard
      have hzero : (∑ e, |J e - K e|) = 0 :=
        Finset.sum_eq_zero fun e _ => False.elim (hempty.false e)
      simpa only [hzero] using hε
    · have hpos : 0 < Fintype.card κ := Nat.pos_of_ne_zero hcard
      have hmax : max 1 (Fintype.card κ) = Fintype.card κ :=
        max_eq_right hpos
      have hcardReal : (Fintype.card κ : ℝ) ≠ 0 := by exact_mod_cast hcard
      calc
        (∑ e, |J e - K e|) ≤
            ∑ _e : κ, ε / (Fintype.card κ : ℝ) := by
          apply Finset.sum_le_sum
          intro e _
          simpa only [hmax] using hcoeff e
        _ = ε := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ ε hcardReal]
  exact (heisenberg_edge_rounding J K u hu).trans (by linarith)

end ContinuumCoulomb

end OAI
