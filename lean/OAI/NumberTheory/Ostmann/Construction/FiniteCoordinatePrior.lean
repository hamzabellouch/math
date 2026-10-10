import Mathlib.Logic.Equiv.Prod
import OAI.NumberTheory.Ostmann.Construction.FiniteFormulaRenaming

namespace OAI

/-! # Exact resampling under the original finite product law -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def finiteCoordinatePrior {σ A : Type*} [Fintype A]
    (μ : σ → A → ℝ) (i : σ) (F : (σ → A) → ℂ) (x : σ → A) : ℂ :=
  ∑ a, (μ i a : ℂ) * F (Function.update x i a)

noncomputable def finiteCoordinatePriors {σ A : Type*} [Fintype A]
    (μ : σ → A → ℝ) : List σ → ((σ → A) → ℂ) → (σ → A) → ℂ
  | [], F => F
  | i :: l, F => finiteCoordinatePrior μ i (finiteCoordinatePriors μ l F)

theorem finite_prior_splitAt {σ A : Type*} [Fintype σ] [Fintype A]
    (μ : σ → A → ℝ) (F : (σ → A) → ℂ) (i : σ) :
    (∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x) =
      ∑ o : {j : σ // j ≠ i} → A, ((∏ j : {j : σ // j ≠ i}, μ j (o j) : ℝ) : ℂ) *
        ∑ a, (μ i a : ℂ) * F ((Equiv.piSplitAt i (fun _ : σ => A)).symm (a, o)) := by
  let e := Equiv.piSplitAt i (fun _ : σ => A)
  rw [← e.symm.sum_comp (fun x => ((∏ j, μ j (x j) : ℝ) : ℂ) * F x),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hp : (∏ j, μ j (e.symm (a, o) j)) = μ i a * ∏ j : {j : σ // j ≠ i}, μ j (o j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp only [e, Equiv.piSplitAt, Equiv.coe_fn_mk, Equiv.symm_mk]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp only [dite_eq_right j.property]
  change ((∏ j, μ j (e.symm (a, o) j) : ℝ) : ℂ) * F (e.symm (a, o)) = _
  rw [hp, Complex.ofReal_mul]
  ring

theorem piSplitAt_update {σ A : Type*} (i : σ)
    (o : {j : σ // j ≠ i} → A) (a b : A) :
    Function.update ((Equiv.piSplitAt i (fun _ : σ => A)).symm (a, o)) i b =
      (Equiv.piSplitAt i (fun _ : σ => A)).symm (b, o) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, hj]

theorem finite_prior_coordinate_preserves {σ A : Type*} [Fintype σ] [Fintype A]
    (μ : σ → A → ℝ) (i : σ) (hmass : ∑ a, μ i a = 1) (F : (σ → A) → ℂ) :
    (∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * finiteCoordinatePrior μ i F x) =
      ∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x := by
  rw [finite_prior_splitAt μ _ i, finite_prior_splitAt μ F i]
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  simp only [finiteCoordinatePrior, piSplitAt_update]
  have hm : (∑ a, (μ i a : ℂ)) = 1 := by exact_mod_cast hmass
  rw [← Finset.sum_mul, hm, one_mul]

theorem finiteCoordinatePriors_preserves {σ A : Type*} [Fintype σ] [Fintype A]
    (μ : σ → A → ℝ) (hmass : ∀ i, ∑ a, μ i a = 1)
    (l : List σ) (F : (σ → A) → ℂ) :
    (∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * finiteCoordinatePriors μ l F x) =
      ∑ x, ((∏ j, μ j (x j) : ℝ) : ℂ) * F x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    exact (finite_prior_coordinate_preserves μ i (hmass i) _).trans ih

theorem finiteCoordinatePriors_update {σ A : Type*} [Fintype A]
    (μ : σ → A → ℝ) (l : List σ) (F : (σ → A) → ℂ)
    (i : σ) (hi : i ∈ l) (x : σ → A) (a : A) :
    finiteCoordinatePriors μ l F (Function.update x i a) = finiteCoordinatePriors μ l F x := by
  induction l generalizing x with
  | nil => simp at hi
  | cons j l ih =>
    change (∑ b, (μ j b : ℂ) * finiteCoordinatePriors μ l F (Function.update (Function.update x i a) j b)) = _
    by_cases hij : i = j
    · subst j
      simp only [Function.update_idem]
      rfl
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hij
      apply Finset.sum_congr rfl
      intro b _
      rw [Function.update_comm hij]
      exact congrArg ((μ j b : ℂ) * ·) (ih hil (Function.update x j b))

/-- Replacing every coordinate gives exactly the full product-prior mean,
regardless of the chosen order. -/
theorem finiteCoordinatePriors_all {σ A : Type*} [Fintype σ] [Fintype A]
    (μ : σ → A → ℝ) (hmass : ∀ i, ∑ a, μ i a = 1)
    (l : List σ) (hl : ∀ i, i ∈ l) (F : (σ → A) → ℂ) (x : σ → A) :
    finiteCoordinatePriors μ l F x = ∑ y, ((∏ j, μ j (y j) : ℝ) : ℂ) * F y := by
  let H := finiteCoordinatePriors μ l F
  have hc (s : Finset σ) : ∀ x y : σ → A, (∀ i ∉ s, x i = y i) → H x = H y := by
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      exact congrArg H (funext fun i => h i (by simp))
    | @insert i s hi ih =>
      intro x y h
      have hu := finiteCoordinatePriors_update μ l F i (hl i) x (y i)
      apply hu.symm.trans
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · rw [Function.update_of_ne hji]
        exact h j (by simp [hj, hji])
  have hconst (y : σ → A) : H y = H x := hc Finset.univ y x (by simp)
  have hpres := finiteCoordinatePriors_preserves μ hmass l F
  change (∑ y, ((∏ j, μ j (y j) : ℝ) : ℂ) * H y) = _ at hpres
  simp_rw [hconst, ← Finset.sum_mul] at hpres
  have hp : (∑ y : σ → A, (∏ j, μ j (y j) : ℝ)) = 1 := by
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  rw [← Complex.ofReal_sum, hp, Complex.ofReal_one, one_mul] at hpres
  exact hpres

end Ostmann

end OAI
