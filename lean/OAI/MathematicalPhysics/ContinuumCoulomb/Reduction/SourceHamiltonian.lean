import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.Spin
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Signed square-lattice Heisenberg source

The finite source is the field-free Heisenberg problem of
Cubitt–Montanaro–Piddock, *Universal quantum Hamiltonians*,
arXiv:1701.05182v4, Theorem 48, Lemma 47 and Section 10.1.
The coordinate-swap action realizes `2 SWAP - I`. Coefficient-rounding
estimates hold for arbitrary many-spin states, including entangled states.
-/

noncomputable section

namespace ContinuumCoulomb

open scoped BigOperators

abbrev SourceSpinBasis (n : ℕ) := Fin n → Fin 2
abbrev SourceSpinVector (n : ℕ) := SourceSpinBasis n → ℂ

def sourceSpinMass {n : ℕ} (u : SourceSpinVector n) : ℝ :=
  ∑ s, Complex.normSq (u s)

/-- Swap the two selected spin coordinates, leaving every spectator fixed. -/
def sourceSpinSwap {n : ℕ} (i j : Fin n) :
    SourceSpinBasis n ≃ SourceSpinBasis n :=
  Equiv.arrowCongr (Equiv.swap i j) (Equiv.refl (Fin 2))

theorem sourceSpinSwap_apply {n : ℕ} (i j : Fin n)
    (s : SourceSpinBasis n) (k : Fin n) :
    sourceSpinSwap i j s k = s (Equiv.swap i j k) := by
  simp [sourceSpinSwap, Equiv.arrowCongr_apply]

theorem sourceSpinSwap_involutive {n : ℕ} (i j : Fin n) :
    Function.Involutive (sourceSpinSwap i j) := by
  intro s
  funext k
  simp [sourceSpinSwap_apply]

theorem sourceSpinMass_nonneg {n : ℕ} (u : SourceSpinVector n) :
    0 ≤ sourceSpinMass u :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem sourceSpinMass_swap {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u (sourceSpinSwap i j s))) = sourceSpinMass u :=
  (sourceSpinSwap i j).sum_comp (fun s => Complex.normSq (u s))

/-- The expectation of coordinate exchange, taking its real part. -/
def sourceSwapExpectation {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) : ℝ :=
  ∑ s, (star (u s) * u (sourceSpinSwap i j s)).re

theorem sourceSwapExpectation_add_identity {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u s + u (sourceSpinSwap i j s))) =
      2 * sourceSpinMass u + 2 * sourceSwapExpectation i j u := by
  have hpoint (s : SourceSpinBasis n) :
      Complex.normSq (u s + u (sourceSpinSwap i j s)) =
        Complex.normSq (u s) + Complex.normSq (u (sourceSpinSwap i j s)) +
          2 * (star (u s) * u (sourceSpinSwap i j s)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sourceSpinMass_swap]
  unfold sourceSpinMass sourceSwapExpectation
  ring

theorem sourceSwapExpectation_sub_identity {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    (∑ s, Complex.normSq (u s - u (sourceSpinSwap i j s))) =
      2 * sourceSpinMass u - 2 * sourceSwapExpectation i j u := by
  have hpoint (s : SourceSpinBasis n) :
      Complex.normSq (u s - u (sourceSpinSwap i j s)) =
        Complex.normSq (u s) + Complex.normSq (u (sourceSpinSwap i j s)) -
          2 * (star (u s) * u (sourceSpinSwap i j s)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
    ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    sourceSpinMass_swap]
  unfold sourceSpinMass sourceSwapExpectation
  ring

theorem sourceSwapExpectation_bounds {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    -sourceSpinMass u ≤ sourceSwapExpectation i j u ∧
      sourceSwapExpectation i j u ≤ sourceSpinMass u := by
  have hp := sourceSwapExpectation_add_identity i j u
  have hm := sourceSwapExpectation_sub_identity i j u
  have hp0 : 0 ≤ ∑ s, Complex.normSq (u s + u (sourceSpinSwap i j s)) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hm0 : 0 ≤ ∑ s, Complex.normSq (u s - u (sourceSpinSwap i j s)) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  constructor <;> linarith

/-- The local Heisenberg action on the complete `n`-spin Hilbert space. -/
def sourceHeisenbergAction {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) :
    SourceSpinVector n :=
  fun s => 2 * u (sourceSpinSwap i j s) - u s

/-- The real quadratic form of the local Heisenberg interaction. -/
def sourceHeisenbergForm {n : ℕ} (i j : Fin n) (u : SourceSpinVector n) : ℝ :=
  ∑ s, (star (u s) * sourceHeisenbergAction i j u s).re

theorem sourceHeisenbergForm_eq {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    sourceHeisenbergForm i j u =
      2 * sourceSwapExpectation i j u - sourceSpinMass u := by
  have hpoint (s : SourceSpinBasis n) :
      (star (u s) * sourceHeisenbergAction i j u s).re =
        2 * (star (u s) * u (sourceSpinSwap i j s)).re - Complex.normSq (u s) := by
    simp [sourceHeisenbergAction, Complex.mul_re, Complex.normSq_apply, Complex.star_def]
    ring
  simp only [sourceHeisenbergForm, hpoint, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sourceSwapExpectation, sourceSpinMass]

theorem sourceHeisenbergForm_bounds {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    -3 * sourceSpinMass u ≤ sourceHeisenbergForm i j u ∧
      sourceHeisenbergForm i j u ≤ sourceSpinMass u := by
  obtain ⟨hl, hu⟩ := sourceSwapExpectation_bounds i j u
  rw [sourceHeisenbergForm_eq]
  constructor <;> linarith

theorem sourceHeisenbergForm_abs_le {n : ℕ}
    (i j : Fin n) (u : SourceSpinVector n) :
    |sourceHeisenbergForm i j u| ≤ 3 * sourceSpinMass u := by
  obtain ⟨hl, hu⟩ := sourceHeisenbergForm_bounds i j u
  have hn := sourceSpinMass_nonneg u
  apply abs_le.mpr
  constructor <;> linarith

/-- The signed rational field-free square-lattice source input.  Polynomial
size/weight bounds are properties of the published reduction, not extra
one-site terms or restrictions on the variational spin states. -/
structure SquareLatticeHeisenberg where
  vertices : ℕ
  vertices_pos : 0 < vertices
  coordinate : Fin vertices → ℤ × ℤ
  coordinate_injective : Function.Injective coordinate
  edges : ℕ
  left : Fin edges → Fin vertices
  right : Fin edges → Fin vertices
  adjacent : ∀ e,
    Int.natAbs ((coordinate (left e)).1 - (coordinate (right e)).1) +
      Int.natAbs ((coordinate (left e)).2 - (coordinate (right e)).2) = 1
  edge_simple : ∀ e f, e ≠ f →
    ¬(left e = left f ∧ right e = right f) ∧
      ¬(left e = right f ∧ right e = left f)
  coefficient : Fin edges → ℚ
  lower : ℚ
  upper : ℚ
  gap_pos : lower < upper

theorem SquareLatticeHeisenberg.edge_ne (d : SquareLatticeHeisenberg)
    (e : Fin d.edges) : d.left e ≠ d.right e := by
  intro heq
  have h := d.adjacent e
  rw [heq] at h
  simp at h

/-- Complete finite Hamiltonian, with no magnetic or one-site terms. -/
def sourceHamiltonian (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) : SourceSpinVector d.vertices :=
  fun s => ∑ e, (d.coefficient e : ℂ) *
    sourceHeisenbergAction (d.left e) (d.right e) u s

def sourceHamiltonianForm (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) : ℝ :=
  ∑ e, (d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u

/-- Real quadratic form of the explicitly defined complete Hamiltonian. -/
theorem sourceHamiltonianForm_eq_expectation (d : SquareLatticeHeisenberg)
    (u : SourceSpinVector d.vertices) :
    sourceHamiltonianForm d u =
      (∑ s, star (u s) * sourceHamiltonian d u s).re := by
  unfold sourceHamiltonian sourceHamiltonianForm sourceHeisenbergForm
  simp only [Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro e _
  simp [Complex.mul_re, Complex.star_def]
  ring

/-- Variational source energy over all normalized spin states. -/
def sourceGroundEnergy (d : SquareLatticeHeisenberg) : EReal :=
  sInf {e | ∃ u : SourceSpinVector d.vertices,
    sourceSpinMass u = 1 ∧ e = (sourceHamiltonianForm d u : EReal)}

/-- Rounding arbitrary signed coefficients incurs the sum of the local
`3|ΔJ|` errors, for the actual complete many-spin state. -/
theorem sourceHamiltonianForm_rounding
    (d : SquareLatticeHeisenberg) (rounded : Fin d.edges → ℝ)
    (u : SourceSpinVector d.vertices) (hu : sourceSpinMass u = 1) :
    |sourceHamiltonianForm d u -
      ∑ e, rounded e * sourceHeisenbergForm (d.left e) (d.right e) u| ≤
      3 * ∑ e, |(d.coefficient e : ℝ) - rounded e| := by
  unfold sourceHamiltonianForm
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ e, ((d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u -
        rounded e * sourceHeisenbergForm (d.left e) (d.right e) u)| ≤
        ∑ e, |(d.coefficient e : ℝ) * sourceHeisenbergForm (d.left e) (d.right e) u -
          rounded e * sourceHeisenbergForm (d.left e) (d.right e) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, 3 * |(d.coefficient e : ℝ) - rounded e| := by
      apply Finset.sum_le_sum
      intro e _
      rw [← sub_mul, abs_mul]
      have h := sourceHeisenbergForm_abs_le (d.left e) (d.right e) u
      rw [hu, mul_one] at h
      nlinarith [abs_nonneg ((d.coefficient e : ℝ) - rounded e)]
    _ = 3 * ∑ e, |(d.coefficient e : ℝ) - rounded e| := (Finset.mul_sum _ _ _).symm

end ContinuumCoulomb

end

end OAI
