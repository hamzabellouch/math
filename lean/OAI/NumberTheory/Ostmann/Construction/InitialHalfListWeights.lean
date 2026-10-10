import OAI.NumberTheory.Ostmann.Construction.InitialLogSumRate
import OAI.NumberTheory.Ostmann.Construction.HalfPrimeFactorization

namespace OAI

/-! # The two independent cutoff weights in an initial half-list -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialLogSumWeight {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) : ℝ :=
  logCellProfile ((∑ i, Real.log (value (x i) : ℝ)) - c)

theorem initialLogSumWeight_nonneg {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    0 ≤ initialLogSumWeight value c x := logCellProfile_nonneg _

theorem initialLogSumWeight_le_one {A : Type*} {n : ℕ}
    (value : A → ℕ) (c : ℝ) (x : Fin n → A) :
    initialLogSumWeight value c x ≤ 1 := logCellProfile_le_one _

/-- Joining the bulk and spectator groups preserves the two weights and
both balanced events under their original independent priors. -/
theorem balancedHalfMass_append {A : Type*} [Fintype A] (b d : ℕ)
    (μ : Fin b → A → ℝ) (ν : Fin d → A → ℝ)
    (goodB : Fin b → A → Prop) (goodD : Fin d → A → Prop)
    (wB : (Fin b → A) → ℝ) (wD : (Fin d → A) → ℝ) :
    (∑ x ∈ balancedTupleSet (b + d) (Fin.append goodB goodD),
      productPrior (Fin.append μ ν) x *
        (wB (fun i => x (i.castAdd d)) * wD (fun i => x (i.natAdd b)))) =
      (∑ x ∈ balancedTupleSet b goodB, productPrior μ x * wB x) *
        ∑ x ∈ balancedTupleSet d goodD, productPrior ν x * wD x := by
  simp only [balancedTupleSet, Finset.sum_filter]
  let e : (Fin b → A) × (Fin d → A) ≃ (Fin (b + d) → A) := Fin.appendEquiv b d
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  change (if ∀ i, Fin.append goodB goodD i (Fin.append x y i) then
      productPrior (Fin.append μ ν) (Fin.append x y) *
        (wB (fun i => Fin.append x y (i.castAdd d)) * wD (fun i => Fin.append x y (i.natAdd b)))
      else 0) = _
  simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, productPrior_append]
  by_cases hB : ∀ i, goodB i (x i) <;> by_cases hD : ∀ i, goodD i (y i) <;>
    simp [hB, hD]
  ring

/-- The two selected cutoffs together retain a fixed exponential amount of
balanced mass. Their product is still a weight, not a conditioned law. -/
theorem balancedHalfMass_log_weights_lower {A : Type*} [Fintype A] (b d m : ℕ)
    (value : A → ℕ) (μ : Fin b → A → ℝ) (ν : Fin d → A → ℝ)
    (goodB : Fin b → A → Prop) (goodD : Fin d → A → Prop)
    (cb cd C : ℝ)
    (hB : Real.exp (-C * m) ≤
      ∑ x ∈ balancedTupleSet b goodB, productPrior μ x * initialLogSumWeight value cb x)
    (hD : Real.exp (-C * m) ≤
      ∑ x ∈ balancedTupleSet d goodD, productPrior ν x * initialLogSumWeight value cd x) :
    Real.exp (-(2 * C) * m) ≤
      ∑ x ∈ balancedTupleSet (b + d) (Fin.append goodB goodD),
        productPrior (Fin.append μ ν) x *
          (initialLogSumWeight value cb (fun i => x (i.castAdd d)) *
            initialLogSumWeight value cd (fun i => x (i.natAdd b))) := by
  rw [balancedHalfMass_append]
  have h := mul_le_mul hB hD (Real.exp_nonneg _) ((Real.exp_nonneg _).trans hB)
  apply le_trans _ h
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf
  exact le_refl _

end Ostmann

end OAI
