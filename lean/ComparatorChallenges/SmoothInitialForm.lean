import Mathlib

namespace OAI

open MvPolynomial
namespace PermanentBorder

open Filter
open scoped Topology

abbrev Poly (σ : Type*) := MvPolynomial σ ℂ

noncomputable def affineMatrixPolynomial {σ : Type*} [Fintype σ] (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ) : Poly σ :=
  Matrix.det (fun i j => MvPolynomial.C (A₀ i j) +
    ∑ v : σ, MvPolynomial.C (A v i j) * MvPolynomial.X v)

def HasBorderDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (A : ℕ → σ → Matrix (Fin n) (Fin n) ℂ),
    ∀ d : σ →₀ ℕ, Tendsto
      (fun j => (affineMatrixPolynomial n (A₀ j) (A j)).coeff d)
      atTop (𝓝 (p.coeff d))

def HasExactDeterminant {σ : Type*} [Fintype σ] (n : ℕ) (p : Poly σ) : Prop :=
  0 < n ∧ ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ)
    (A : σ → Matrix (Fin n) (Fin n) ℂ), affineMatrixPolynomial n A₀ A = p

noncomputable def affineSubstitution {σ τ : Type*} [Fintype τ]
    (b : σ → ℂ) (B : σ → τ → ℂ) : Poly σ →ₐ[ℂ] Poly τ :=
  MvPolynomial.aeval (fun v => MvPolynomial.C (b v) +
    ∑ w : τ, MvPolynomial.C (B v w) * MvPolynomial.X w)

theorem smooth_initial_form_lower_bound (d r : ℕ) (g : Poly (Fin d))
    (a : Fin d → ℂ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    (hG : homogeneousComponent r
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) ≠ 0)
    (hlow : ∀ j < r, homogeneousComponent j
      (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g) = 0)
    (hs : ∀ y : Fin d → ℂ,
      eval y (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g)) = 0 →
      (∀ i, eval y (pderiv i (homogeneousComponent r
        (affineSubstitution a (fun i j : Fin d => if i = j then 1 else 0) g))) = 0) →
      y = 0) :
    ∀ n : ℕ,
      (HasBorderDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) ∧
      (HasExactDeterminant n g →
        ((r - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) / (4 * Real.exp 1) ≤ (n : ℝ)) := by
  sorry

end PermanentBorder

end OAI
