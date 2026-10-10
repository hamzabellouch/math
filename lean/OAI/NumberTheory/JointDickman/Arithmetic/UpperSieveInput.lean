import OAI.NumberTheory.JointDickman.Arithmetic.WeightedSieve
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Published finite-event upper sieve

Theorem 2.4 of Kevin Ford, *Sieve Methods Lecture Notes, Spring 2023*,
page 18, https://ford126.web.illinois.edu/sieve2023.pdf, in its general
probability-space formulation (Section 1.2). The sum of absolute remainders
is only over squarefree products at most the sifting bound. No arithmetic
progression estimate or application-specific weight bound is assumed here.
-/

namespace JointDickman

open Finset

/-- Mass of the intersection of the events indexed by `D`. -/
noncomputable def sieveIntersection {X : Type*} [Fintype X]
    (E : X → Finset ℕ) (w : X → ℝ) (D : Finset ℕ) : ℝ :=
  ∑ x, if D ⊆ E x then w x else 0

/-- Ford's remainder `r_d`, with `D` the prime factors of `d`. -/
noncomputable def sieveRemainder {X : Type*} [Fintype X]
    (E : X → Finset ℕ) (w : X → ℝ) (M : ℝ) (g : ℕ → ℝ)
    (D : Finset ℕ) : ℝ := sieveIntersection E w D - M * ∏ p ∈ D, g p

/-- Ford's interval condition `(Ω)`. Primes outside `P` have local density zero. -/
def SieveDimension (P : Finset ℕ) (g : ℕ → ℝ) (κ A z : ℝ) : Prop :=
  ∀ y v : ℝ, 2 ≤ y → y ≤ v → v ≤ z →
    (∏ p ∈ P.filter (fun p : ℕ => y ≤ (p : ℝ) ∧ (p : ℝ) ≤ v), (1 - g p)⁻¹) ≤
      (Real.log v / Real.log y) ^ κ * Real.exp (A / Real.log y)

namespace PublishedInputs

/-- Ford 2023, Theorem 2.4, specialized to a finite nonnegative population.
The constant is independent of the population, events, densities and bound.
The parameter `M` is the main-term mass `X` in the source; its difference
from the actual population mass is retained in the `D = ∅` remainder. -/
def FordUpperSieveInput : Prop :=
  ∀ κ A : ℝ, 0 < κ → 0 ≤ A → ∃ C : ℝ, 0 < C ∧
    ∀ (X : Type) [Fintype X] (P : Finset ℕ) (E : X → Finset ℕ)
      (w : X → ℝ) (M z : ℝ) (g : ℕ → ℝ),
      2 ≤ z → 0 ≤ M → (∀ x, 0 ≤ w x) →
      (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z) →
      (∀ p ∈ P, 0 ≤ g p ∧ g p < 1) →
      SieveDimension P g κ A z →
      (∑ x, w x * avoidsSelected P (E x)) ≤
        C * M * (∏ p ∈ P, (1 - g p)) +
          ∑ D ∈ P.powerset.filter (fun D => (∏ p ∈ D, p : ℕ) ≤ z),
            |sieveRemainder E w M g D|

end PublishedInputs

/-- Decreasing the local densities preserves Ford's dimension condition. -/
theorem SieveDimension.mono {P : Finset ℕ} {g h : ℕ → ℝ} {κ A z : ℝ}
    (hd : SieveDimension P g κ A z)
    (hgh : ∀ p ∈ P, h p ≤ g p) (hg : ∀ p ∈ P, g p < 1) :
    SieveDimension P h κ A z := by
  intro y v hy hyv hvz
  apply le_trans _ (hd y v hy hyv hvz)
  apply prod_le_prod₀
  · intro p hp
    have hpg := hg p (mem_filter.mp hp).1
    exact inv_nonneg.mpr (by linarith [hgh p (mem_filter.mp hp).1])
  · intro p hp
    have hpg := hg p (mem_filter.mp hp).1
    exact inv_anti₀ (by linarith) (by linarith [hgh p (mem_filter.mp hp).1])

/-- Deleting sieve primes also preserves the dimension condition. -/
theorem SieveDimension.subset {P S : Finset ℕ} {g : ℕ → ℝ} {κ A z : ℝ}
    (hd : SieveDimension P g κ A z) (hS : S ⊆ P)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p < 1) :
    SieveDimension S g κ A z := by
  intro y v hy hyv hvz
  apply le_trans _ (hd y v hy hyv hvz)
  apply prod_le_prod_of_subset_of_one_le₀
  · intro p hp
    exact mem_filter.mpr ⟨hS (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  · intro p hp
    exact inv_nonneg.mpr (by linarith [(hg p (hS (mem_filter.mp hp).1)).2])
  · intro p hp _
    exact (one_le_inv₀ (by linarith [(hg p (mem_filter.mp hp).1).2])).mpr
      (by linarith [(hg p (mem_filter.mp hp).1).1])

end JointDickman

end OAI
