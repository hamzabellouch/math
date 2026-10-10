import OAI.Combinatorics.SharpThreshold.FourierRestriction
import OAI.Combinatorics.SharpThreshold.FourierSupportSplit

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Exact averaging of any selected family of conditional Fourier levels. -/
theorem restricted_mass_average {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (L : Finset (Finset ι)) :
    (∑ y : κ → Bool, weight p y *
      ∑ A ∈ L, (coeff p (fun x => f (Sum.elim x y)) A) ^ 2) =
      ∑ A ∈ L, ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  exact restricted_coeff_sq_average hp hp1 f A

/-- The restriction identity reindexed by full supports. The condition is
placed only on the free-coordinate part, never on exterior Fourier degree. -/
theorem restricted_mass_condition {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (P : Finset ι → Prop) [DecidablePred P] :
    (∑ y : κ → Bool, weight p y *
      ∑ A : Finset ι, if P A then
        (coeff p (fun x => f (Sum.elim x y)) A) ^ 2 else 0) =
      ∑ S : Finset (ι ⊕ κ), if P S.toLeft then (coeff p f S) ^ 2 else 0 := by
  classical
  calc
    _ = ∑ A : Finset ι, if P A then
        ∑ D : Finset κ, (coeff p f (A.disjSum D)) ^ 2 else 0 := by
      simpa only [Finset.sum_filter] using
        restricted_mass_average hp hp1 f (Finset.univ.filter P)
    _ = _ := (sum_support_condition_disjSum (fun S => (coeff p f S) ^ 2) P).symm

/-- Literal real-valued conditional degree cutoff, including the case `k < 1`. -/
theorem restricted_low_degree_mass_average {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι ⊕ κ → Bool) → ℝ) (k : ℝ) :
    (∑ y : κ → Bool, weight p y *
      ∑ A : Finset ι, if 1 ≤ A.card ∧ (A.card : ℝ) ≤ k then
        (coeff p (fun x => f (Sum.elim x y)) A) ^ 2 else 0) =
      ∑ S : Finset (ι ⊕ κ), if 1 ≤ S.toLeft.card ∧ (S.toLeft.card : ℝ) ≤ k then
        (coeff p f S) ^ 2 else 0 := by
  classical
  exact restricted_mass_condition hp hp1 f (fun A => 1 ≤ A.card ∧ (A.card : ℝ) ≤ k)

end Problem313.BiasedFourier

end

end OAI
