import OAI.Combinatorics.EditApproximation.Refinement.PhysicalParentDraw

namespace OAI

/-! Exact coordinate-refresh identities for finite product probability laws. -/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

section FiniteProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, MeasurableSpace (X i)]
  [∀ i, MeasurableSingletonClass (X i)]
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Refreshing one coordinate with its own independent law preserves the
complete finite product law. -/
theorem finite_pi_update_map (i : ι) :
    ((Measure.pi μ).prod (μ i)).map
      (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2) = Measure.pi μ := by
  apply Eq.symm
  apply Measure.pi_eq
  intro sets hsets
  have hpreimage : (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2) ⁻¹'
      Set.univ.pi sets = (Set.univ.pi (Function.update sets i Set.univ)) ×ˢ sets i := by
    ext pair
    constructor
    · intro h
      constructor
      · intro j _
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self, Set.mem_univ]
        · simpa only [Function.update_of_ne hji] using h j (Set.mem_univ j)
      · simpa only [Function.update_self] using h i (Set.mem_univ i)
    · rintro ⟨hold, hfresh⟩ j _
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hfresh
      · simpa only [Function.update_of_ne hji] using hold j (Set.mem_univ j)
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.univ_pi hsets),
    hpreimage, Measure.prod_prod, Measure.pi_pi]
  rw [← prod_erase_mul (s := univ) (fun j => μ j (Function.update sets i Set.univ j)) (mem_univ i),
    ← prod_erase_mul (s := univ) (fun j => μ j (sets j)) (mem_univ i)]
  simp only [Function.update_self, measure_univ, mul_one]
  congr 1
  apply prod_congr rfl
  intro j hj
  simp only [Function.update_of_ne (ne_of_mem_erase hj)]

/-- Integrating a fresh coordinate, then the complete original array, is
exactly integration in the original product law. -/
theorem finite_pi_integral_update (i : ι) (payoff : (∀ j, X j) → ℝ) :
    (∫ original, ∫ fresh, payoff (Function.update original i fresh) ∂μ i ∂Measure.pi μ) =
      ∫ original, payoff original ∂Measure.pi μ := by
  rw [← integral_prod (fun pair : (∀ j, X j) × X i =>
    payoff (Function.update pair.1 i pair.2)) (.of_finite)]
  have hmap := finite_pi_update_map μ i
  have hintegral := integral_map_of_stronglyMeasurable
    (μ := (Measure.pi μ).prod (μ i))
    (measurable_of_finite (fun pair : (∀ j, X j) × X i => Function.update pair.1 i pair.2))
    (measurable_of_finite payoff).stronglyMeasurable
  rw [hmap] at hintegral
  exact hintegral.symm

/-- Two independent refreshed coordinates provide the local parent law.
The original arrays may still contain their previous values at those keys. -/
theorem finite_pi_integral_update_pair (i j : ι) (payoff : (∀ k, X k) → ℝ) :
    (∫ original, ∫ fresh : X i × X j,
      payoff (Function.update (Function.update original i fresh.1) j fresh.2)
        ∂(μ i).prod (μ j) ∂Measure.pi μ) =
      ∫ original, payoff original ∂Measure.pi μ := by
  have hinner original : (∫ fresh : X i × X j,
      payoff (Function.update (Function.update original i fresh.1) j fresh.2) ∂(μ i).prod (μ j)) =
      ∫ first, ∫ second, payoff (Function.update (Function.update original i first) j second) ∂μ j ∂μ i :=
    integral_prod _ (.of_finite)
  simp_rw [hinner]
  rw [finite_pi_integral_update μ i
    (fun original => ∫ second, payoff (Function.update original j second) ∂μ j)]
  exact finite_pi_integral_update μ j payoff

/-- A pointwise bound after exact coordinate refresh integrates to the
unconditional bound in the original global product. -/
theorem finite_pi_integral_bound_of_update_pair (i j : ι)
    (payoff budget : (∀ k, X k) → ℝ)
    (hbound : ∀ original, (∫ fresh : X i × X j,
      payoff (Function.update (Function.update original i fresh.1) j fresh.2) ∂(μ i).prod (μ j)) ≤
        budget original) :
    (∫ original, payoff original ∂Measure.pi μ) ≤ ∫ original, budget original ∂Measure.pi μ := by
  rw [← finite_pi_integral_update_pair μ i j payoff]
  exact integral_mono (.of_finite) (.of_finite) hbound

end FiniteProduct

end EditApproximation

end OAI
