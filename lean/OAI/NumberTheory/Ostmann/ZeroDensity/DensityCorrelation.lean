import OAI.NumberTheory.Ostmann.Characters.PrimeCRTFourier

namespace OAI

/-! # The prime-by-prime correlation bound for centered densities -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- Which of the two squarefree divisors contains a prime of their union. -/
inductive CorrelationSide where
  | left
  | right
  | both

/-- Extend the local transform to an unrestricted prime index. The value at
zero is immaterial; all applications index positive primes. -/
noncomputable def primeDensityFourier (f : ∀ p : ℕ, ZMod p → ℂ) (p : ℕ) : ZMod p → ℂ :=
  if h : 0 < p then @densityFourier p ⟨h.ne'⟩ (f p) else fun _ => 0

theorem primeDensityFourier_eq {p : ℕ} [NeZero p] (f : ∀ p : ℕ, ZMod p → ℂ) :
    primeDensityFourier f p = densityFourier (f p) := by
  simp only [primeDensityFourier, dite_eq_left (Nat.pos_of_ne_zero (NeZero.ne p))]

noncomputable def correlationPrimeFactor (f : ∀ p : ℕ, ZMod p → ℂ)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) (p : ℕ) (x : ZMod p) : ℂ :=
  match side p with
  | .left => primeDensityFourier f p ((a p : ZMod p) * x)
  | .right => conj (primeDensityFourier f p ((b p : ZMod p) * x))
  | .both => primeDensityFourier f p ((a p : ZMod p) * x) *
      conj (primeDensityFourier f p ((b p : ZMod p) * x))

noncomputable def correlationPrimeBound (side : ℕ → CorrelationSide) (p : ℕ) : ℝ :=
  match side p with
  | .left => (Real.sqrt (p : ℝ))⁻¹
  | .right => (Real.sqrt (p : ℝ))⁻¹
  | .both => 1

theorem correlationPrimeBound_nonneg (side : ℕ → CorrelationSide) (p : ℕ) :
    0 ≤ correlationPrimeBound side p := by
  unfold correlationPrimeBound
  split <;> positivity

theorem correlationPrimeFactor_coefficient_le {p : ℕ} [NeZero p]
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) (u : ZMod p) :
    ‖additiveFourier (correlationPrimeFactor f side a b p) u‖ ≤
      correlationPrimeBound side p := by
  unfold correlationPrimeFactor correlationPrimeBound
  cases side p with
  | left =>
    simp only [primeDensityFourier_eq]
    exact densityFourier_unit_coefficient_le (f p) hf (a p) u
  | right =>
    simp only [primeDensityFourier_eq, additiveFourier_conj, Complex.norm_conj]
    exact densityFourier_unit_coefficient_le (f p) hf (b p) (-u)
  | both =>
    simp only [primeDensityFourier_eq]
    exact densityFourier_unit_cross_le_one (f p) (f p) hf hf (a p) (b p) u

/-- This proves the local-product form of the manuscript's `A_{d,d'}`,
with no analytic hypothesis on the density beyond its pointwise bound. -/
theorem density_correlation_coefficient_bound (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ ps, ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ) :
    let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
    ∀ u, ‖additiveFourier (primeCRTFunction ps hp hc (correlationPrimeFactor f side a b)) u‖ ≤
      (ps.map (correlationPrimeBound side)).prod := by
  apply primeCRTFunction_coefficient_le
  · intro p _
    exact correlationPrimeBound_nonneg side p
  · intro p h u
    let : NeZero p := ⟨(hp p h).ne_zero⟩
    exact correlationPrimeFactor_coefficient_le f (hf p h) side a b u

/-- The weighted linear-phase estimate for the actual product of local
correlation factors. -/
theorem density_correlation_weighted_sum_bound (ps : List ℕ)
    (hp : ∀ p ∈ ps, p.Prime) (hc : ps.Pairwise Nat.Coprime)
    (f : ∀ p : ℕ, ZMod p → ℂ) (hf : ∀ p ∈ ps, ∀ x, ‖f p x‖ ≤ 1)
    (side : ℕ → CorrelationSide) (a b : ∀ p : ℕ, (ZMod p)ˣ)
    (α : ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n *
      (primeCRTFunction ps hp hc (correlationPrimeFactor f side a b) (n : ZMod ps.prod) *
        realAdditivePhase α ^ n)‖ ≤
      discreteVariation w N * (2 * (ps.map (correlationPrimeBound side)).prod *
        ((N : ℝ) + ps.prod * (1 + Real.log ps.prod))) := by
  let : NeZero ps.prod := ⟨(prime_list_prod_pos ps hp).ne'⟩
  apply weighted_periodic_linear_phase_bound
  · exact List.prod_nonneg (fun x hx => by
      obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
      exact correlationPrimeBound_nonneg side p)
  · exact density_correlation_coefficient_bound ps hp hc f hf side a b

end Ostmann

end OAI
