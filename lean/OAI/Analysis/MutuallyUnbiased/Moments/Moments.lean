import Mathlib.Data.Fintype.BigOperators
import OAI.Analysis.MutuallyUnbiased.Matrix.Hadamard
import OAI.Analysis.MutuallyUnbiased.Moments.AverageAlgebra

namespace OAI

/-! Finite injective moments of Section 2 of the exact companion.
Both orientations are retained with weight 1/2, including when H = Hᵀ. -/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MUB6

def exponentMonomial {p q : ℕ} (H : CMatrix) (A : Matrix (Fin p) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) : ℂ :=
  ∏ u, ∏ v, H (ρ u) (κ v) ^ A u v

def injectiveMoment {p q : ℕ} (H : CMatrix) (A : Matrix (Fin p) (Fin q) ℤ) : ℝ :=
  average (fun s : (Fin p ↪ Coord) × (Fin q ↪ Coord) =>
    ((exponentMonomial H A s.1 s.2).re +
      (exponentMonomial H.transpose A s.1 s.2).re) / 2)

theorem exponentMonomial_norm {p q : ℕ} (H : CMatrix)
    (hH : ∀ i j, Complex.normSq (H i j) = 1) (A : Matrix (Fin p) (Fin q) ℤ)
    (ρ : Fin p ↪ Coord) (κ : Fin q ↪ Coord) :
    ‖exponentMonomial H A ρ κ‖ = 1 := by
  simp [exponentMonomial, unit_norm (hH _ _)]

theorem injectiveMoment_abs_le_one {p q : ℕ} {H : CMatrix} (hH : IsHadamard H)
    (A : Matrix (Fin p) (Fin q) ℤ) : |injectiveMoment H A| ≤ 1 := by
  apply abs_average_le_one
  intro s
  have h₁ : |(exponentMonomial H A s.1 s.2).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq (exponentMonomial_norm H hH.1 A s.1 s.2)
  have h₂ : |(exponentMonomial H.transpose A s.1 s.2).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans_eq
      (exponentMonomial_norm H.transpose (fun i j => hH.1 j i) A s.1 s.2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_add_le (exponentMonomial H A s.1 s.2).re
    (exponentMonomial H.transpose A s.1 s.2).re
  linarith

/-- Equation (pair-average), with the two orientations counted separately. -/
def pairAverage (H : CMatrix) (F : CMatrix → ℝ) : ℝ :=
  average (fun π : Equiv.Perm Coord =>
    (F (fun i j => H (π i) j) + F (fun i j => H j (π i))) / 2)

theorem pairAverage_nonneg (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) : 0 ≤ pairAverage H F := by
  apply average_nonneg
  intro π
  exact div_nonneg (add_nonneg (hF _) (hF _)) (by norm_num)

theorem pairAverage_zero_terms (H : CMatrix) (F : CMatrix → ℝ)
    (hF : ∀ K, 0 ≤ F K) (hzero : pairAverage H F = 0) (π : Equiv.Perm Coord) :
    F (fun i j => H (π i) j) = 0 ∧ F (fun i j => H j (π i)) = 0 := by
  have ht := (average_eq_zero_iff _
    (fun p : Equiv.Perm Coord => div_nonneg
      (add_nonneg (hF (fun i j => H (p i) j)) (hF (fun i j => H j (p i))))
      (by norm_num))).mp hzero π
  have h₁ := hF (fun i j => H (π i) j)
  have h₂ := hF (fun i j => H j (π i))
  constructor <;> linarith

end MUB6

end

end OAI
