import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.PretentiousDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace OAI

/-!
# Short-interval estimates for multiplicative functions

The estimates specialize K. Matomäki, M. Radziwiłł and T. Tao,
*An averaged form of Chowla's conjecture*, Algebra & Number Theory 9 (2015),
2167–2196, corrected arXiv:1503.05121v3 (1 March 2022), Theorems 1.3 and 1.7;
DOI 10.2140/ant.2015.9.2167.

The frequency is fixed during the integral. A uniform lower bound on the
squared pretentious distances replaces the infimum in Theorem 1.7.
-/

namespace TwoPointCorrelations

open scoped BigOperators
open MeasureTheory

/-- The usual additive character `e(αn) = exp(2πiαn)`. -/
noncomputable def additiveCharacter (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * α * (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Sum over the integers `y < n ≤ y+H` (for the nonnegative starting points
used in the integral). -/
noncomputable def shortExponentialSum (b : ℕ → ℂ) (H : ℕ) (α y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (Nat.floor y + 1) (Nat.floor (y + (H : ℝ))),
    b n * additiveCharacter α n

/-- The mean over interval origins, with a single fixed frequency. -/
noncomputable def shortExponentialIntegral (b : ℕ → ℂ) (X H : ℕ) (α : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..(X : ℝ), ‖shortExponentialSum b H α y‖

/-- The character-modulus cutoff in corrected MRT Theorem 1.7. -/
noncomputable def mrtModulusCutoff (X H : ℕ) : ℝ :=
  min ((Real.log (X : ℝ)) ^ (1 / (125 : ℝ))) ((Real.log (H : ℝ)) ^ (5 : ℕ))

/-- The error shared by MRT Theorems 1.3 and 1.7. -/
noncomputable def mrtShortError (X H : ℕ) : ℝ :=
  Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) +
    (Real.log (X : ℝ)) ^ (-1 / (700 : ℝ))

/-- The exact range of lower bounds required by corrected MRT Theorem 1.7. -/
def MRTDistanceLowerBound (b : ℕ → ℂ) (X H : ℕ) (M : ℝ) : Prop :=
  ∀ (q : ℕ), 0 < q → (q : ℝ) ≤ mrtModulusCutoff X H →
    ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), |t| ≤ (X : ℝ) →
      M ≤ squaredDistance b (characterTwist χ t) X

/-- Natural-cutoff specialization of corrected MRT Theorem 1.7, with an
explicit lower bound `M` in place of the infimum of squared distances. -/
def MRTShortExponentialInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), 10 ≤ H → H ≤ X →
    ∀ (b : ℕ → ℂ), Multiplicative b → OneBounded b →
      ∀ M : ℝ, MRTDistanceLowerBound b X H M → ∀ α : ℝ,
        shortExponentialIntegral b X H α ≤
          C * (H : ℝ) * (X : ℝ) * (Real.exp (-M / 20) + mrtShortError X H)

/-- Natural-cutoff Liouville specialization of MRT Theorem 1.3. Endpoint
conventions differ only at a measure-zero set of interval origins. -/
def MRTLiouvilleShortInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), 10 ≤ H → H ≤ X → ∀ α : ℝ,
    shortExponentialIntegral liouville X H α ≤
      C * (H : ℝ) * (X : ℝ) * mrtShortError X H

/-- At a fixed modulus cutoff, uniform nonpretentiousness gives one bound
simultaneously for every character and every permitted finite-prime change. -/
theorem UniformlyNonpretentious.bounded_moduli {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (P : Finset ℕ) (Q : ℕ) (K : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ q : ℕ, 0 < q → q ≤ Q →
      ∀ (χ : DirichletCharacter ℂ q) (b : ℕ → ℂ), OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) →
        ∀ t : ℝ, |t| ≤ (N : ℝ) → K ≤ squaredDistance b (characterTwist χ t) N := by
  classical
  let ι := (Σ q : Fin Q, DirichletCharacter ℂ (q.val + 1))
  have hfamily := hfnp.finite_family (ι := ι) hf P
    (fun i => i.1.val + 1) (fun _ => Nat.succ_pos _) (fun i => i.2) K
  filter_upwards [hfamily] with N hN
  intro q hq hqQ χ b hb heq t ht
  cases q with
  | zero => omega
  | succ q =>
      exact hN ⟨⟨q, Nat.lt_of_succ_le hqQ⟩, χ⟩ b hb heq t ht

/-- Fixing the short interval length leaves only finitely many moduli in the
published theorem. Thus the entire MRT distance hypothesis holds uniformly. -/
theorem UniformlyNonpretentious.eventually_mrt_lower_bound {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f)
    (P : Finset ℕ) (H : ℕ) (M : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ → ℂ, OneBounded b →
      (∀ p, Nat.Prime p → p ∉ P → b p = f p) → MRTDistanceLowerBound b N H M := by
  have hfinite := hfnp.bounded_moduli hf P (Nat.ceil ((Real.log (H : ℝ)) ^ (5 : ℕ))) M
  filter_upwards [hfinite] with N hN
  intro b hb heq q hq hqCutoff χ t ht
  have hqQ : q ≤ Nat.ceil ((Real.log (H : ℝ)) ^ (5 : ℕ)) := by
    exact_mod_cast hqCutoff.trans ((min_le_right _ _).trans (Nat.le_ceil _))
  exact hN q hq hqQ χ b hb heq t ht

/-- The published short-sum estimate immediately gives a bound on the
normalized mean, without moving a frequency supremum into the integral. -/
theorem MRTShortExponentialInput.normalized (hMRT : MRTShortExponentialInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X H : ℕ), 10 ≤ H → H ≤ X →
      ∀ (b : ℕ → ℂ), Multiplicative b → OneBounded b →
        ∀ M : ℝ, MRTDistanceLowerBound b X H M → ∀ α : ℝ,
          shortExponentialIntegral b X H α / ((H : ℝ) * (X : ℝ)) ≤
            C * (Real.exp (-M / 20) + mrtShortError X H) := by
  obtain ⟨C, hC, hbound⟩ := hMRT
  refine ⟨C, hC, ?_⟩
  intro X H hH hX b hmult hbounded M hM α
  have hHp : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply (div_le_iff₀ (mul_pos hHp hXp)).mpr
  convert hbound X H hH hX b hmult hbounded M hM α using 1
  ring

/-- A genuine conditional consequence of published MRT Theorem 1.7:
finite local modifications preserve the uniform short-sum estimate at every
fixed short-interval length. The estimate is uniform over all modifications
and frequencies, with the frequency still outside the integral. -/
theorem MRTShortExponentialInput.finite_prime_changes
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) (P : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℕ), 10 ≤ H → ∀ M : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop, ∀ b : ℕ → ℂ,
        Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
          shortExponentialIntegral b N H α / ((H : ℝ) * (N : ℝ)) ≤
            C * (Real.exp (-M / 20) + mrtShortError N H) := by
  obtain ⟨C, hC, hbound⟩ := hMRT.normalized
  refine ⟨C, hC, ?_⟩
  intro H hH M
  filter_upwards [hfnp.eventually_mrt_lower_bound hf P H M,
    Filter.eventually_ge_atTop H] with N hN hHN
  intro b hmult hb heq α
  exact hbound N H hH hHN b hmult hb M (hN b hb heq) α

end TwoPointCorrelations

end OAI
