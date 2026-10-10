import OAI.NumberTheory.Ostmann.Construction.FinalPermutationComparison

namespace OAI

/-! # Final reassignments preserve the original independent sampling law -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def finalBulkPrior {Y A : Type*} (n m : ℕ)
    (ν : Y → ℝ) (μ : A → ℝ) (x : Y × ((ParityPathSum n × Fin m) → A)) : ℝ :=
  ν x.1 * identicalBulkPrior μ x.2

def finalSamplePerm {Y A : Type*} {n m : ℕ} (e : FinalParityReassignments n m) :
    (Y × ((ParityPathSum n × Fin m) → A)) ≃ (Y × ((ParityPathSum n × Fin m) → A)) :=
  Equiv.prodCongr (Equiv.refl Y) (bulkArrayEquiv (paritySlotPerm e))

def finalReassignedValue {Y A : Type*} {n m : ℕ}
    (F : (Y × ((ParityPathSum n × Fin m) → A)) → ℂ)
    (e : FinalParityReassignments n m) (x : Y × ((ParityPathSum n × Fin m) → A)) : ℂ :=
  F (finalSamplePerm e x)

theorem finalBulkPrior_preserved {Y A : Type*} {n m : ℕ}
    (ν : Y → ℝ) (μ : A → ℝ) (e : FinalParityReassignments n m)
    (x : Y × ((ParityPathSum n × Fin m) → A)) :
    finalBulkPrior n m ν μ (finalSamplePerm e x) = finalBulkPrior n m ν μ x := by
  exact congrArg (fun t => ν x.1 * t) (identicalBulkPrior_permute μ (paritySlotPerm e) x.2)

theorem finalBulkPrior_nonneg {Y A : Type*} {n m : ℕ}
    (ν : Y → ℝ) (μ : A → ℝ) (hν : ∀ y, 0 ≤ ν y) (hμ : ∀ a, 0 ≤ μ a)
    (x : Y × ((ParityPathSum n × Fin m) → A)) : 0 ≤ finalBulkPrior n m ν μ x :=
  mul_nonneg (hν x.1) (Finset.prod_nonneg fun i _ => hμ (x.2 i))

theorem finalBulkPrior_mass {Y A : Type*} [Fintype Y] [Fintype A] (n m : ℕ)
    (ν : Y → ℝ) (μ : A → ℝ) (hμ : ∑ a, μ a = 1) :
    (∑ x, finalBulkPrior n m ν μ x) = ∑ y, ν y := by
  have hbulk : (∑ x : (ParityPathSum n × Fin m) → A, identicalBulkPrior μ x) = 1 := by
    simp only [identicalBulkPrior, ← Fintype.prod_sum, hμ, Finset.prod_const_one]
  simp only [finalBulkPrior, Fintype.sum_prod_type, ← Finset.mul_sum, hbulk, mul_one]

/-- All support conditions belong to `F`; no conditional sampling law is used. -/
theorem finalReassignedValue_mean {Y A : Type*} [Fintype Y] [Fintype A] {n m : ℕ}
    (ν : Y → ℝ) (μ : A → ℝ)
    (F : (Y × ((ParityPathSum n × Fin m) → A)) → ℂ)
    (e : FinalParityReassignments n m) :
    (∑ x, (finalBulkPrior n m ν μ x : ℂ) * finalReassignedValue F e x) =
      ∑ x, (finalBulkPrior n m ν μ x : ℂ) * F x := by
  have h := (finalSamplePerm (Y := Y) (A := A) e).sum_comp
    (fun x => (finalBulkPrior n m ν μ x : ℂ) * F x)
  simpa only [finalBulkPrior_preserved, finalReassignedValue] using h

/-- The diagonal norm has the same original prior after reassignment. -/
theorem finalReassignedValue_energy {Y A : Type*} [Fintype Y] [Fintype A] {n m : ℕ}
    (ν : Y → ℝ) (μ : A → ℝ)
    (F : (Y × ((ParityPathSum n × Fin m) → A)) → ℂ)
    (e : FinalParityReassignments n m) :
    (∑ x, finalBulkPrior n m ν μ x * ‖finalReassignedValue F e x‖ ^ 2) =
      ∑ x, finalBulkPrior n m ν μ x * ‖F x‖ ^ 2 := by
  have h := (finalSamplePerm (Y := Y) (A := A) e).sum_comp
    (fun x => finalBulkPrior n m ν μ x * ‖F x‖ ^ 2)
  simpa only [finalBulkPrior_preserved, finalReassignedValue] using h

theorem final_actual_prior_comparison {Y A : Type*} [Fintype Y] [Fintype A] (n m : ℕ)
    (ν : Y → ℝ) (μ : A → ℝ) (hν : ∀ y, 0 ≤ ν y) (hμ : ∀ a, 0 ≤ μ a)
    (hμmass : ∑ a, μ a = 1) (T B E : ℝ) (hT : ∑ y, ν y ≤ T) (hE : 0 ≤ E)
    (F : (Y × ((ParityPathSum n × Fin m) → A)) → ℂ)
    (hpair : ∀ e f : FinalParityReassignments n m,
      ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) *
        (finalReassignedValue F e x * star (finalReassignedValue F f x))‖ ≤
          if e = f then B else E) :
    ‖∑ x, (finalBulkPrior n m ν μ x : ℂ) * F x‖ ^ 2 ≤
      T * (B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + E) := by
  apply final_permutation_comparison n m (finalBulkPrior n m ν μ)
    (finalBulkPrior_nonneg ν μ hν hμ) T B E
    (by simpa only [finalBulkPrior_mass n m ν μ hμmass] using hT) hE
    (finalReassignedValue F) _ (finalReassignedValue_mean ν μ F) hpair

end Ostmann

end OAI
