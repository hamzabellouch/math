import OAI.NumberTheory.Ostmann.Construction.GiantLogMeasures
import OAI.NumberTheory.Ostmann.Construction.TwoGiantIntegralTransport

namespace OAI

/-! # Joint transport of the literal reciprocal-prime and integer sums -/

namespace Ostmann
open MeasureTheory
open scoped BigOperators Classical

noncomputable def primeResidueAtom (q a p : ℕ) : ℝ :=
  if p.Prime ∧ Nat.ModEq q p a then (p : ℝ)⁻¹ else 0

theorem primeResidueAtom_nonneg (q a p : ℕ) : 0 ≤ primeResidueAtom q a p := by
  unfold primeResidueAtom
  split_ifs <;> positivity

theorem complexPrimeInterval_subtype (q a : ℕ) (u v : ℝ) (f : ℝ → ℂ) :
    complexPrimeInterval q a u v f =
      ∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (primeResidueAtom q a p : ℂ) * f (Real.log (p : ℕ)) := by
  rw [Finset.sum_coe_sort (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)
    (fun p : ℕ => (primeResidueAtom q a p : ℂ) * f (Real.log p))]
  unfold complexPrimeInterval primeResidueAtom
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp only [Complex.ofReal_zero, Complex.ofReal_inv, zero_mul, mul_comm]

theorem complexIntegerInterval_subtype (q a : ℕ) (u v G : ℝ) (f : ℝ → ℂ) :
    complexIntegerInterval q a u v G f =
      ∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
        (integerResidueAtom q a G p : ℂ) * f (Real.log (p : ℕ)) := by
  rw [Finset.sum_coe_sort (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊)
    (fun p : ℕ => (integerResidueAtom q a G p : ℂ) * f (Real.log p))]
  unfold complexIntegerInterval
  apply Finset.sum_congr rfl
  intro p _
  exact mul_comm _ _

theorem primeResidueAtom_subtype_mass (q a : ℕ) (u v : ℝ) :
    (∑ p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, primeResidueAtom q a p) =
      reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) := by
  rw [Finset.sum_coe_sort]
  rfl

/-- The original finite sums are transported directly. All real measurability
and integrability requirements are discharged from the bounded kernel. -/
theorem prime_pair_integral_transport (q a b : ℕ) (u v r s : ℝ)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H))
    (K : ℝ) (hK : ∀ x y, ‖H x y‖ ≤ K) (δ ε : ℝ)
    (hleft : ∀ y, ‖complexPrimeInterval q a u v (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ δ)
    (hright : ∀ x, ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ ε) :
    ‖complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x => H x y)) -
      ∫ x, ∫ y, H x y ∂ν ∂μ‖ ≤
      δ * reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + ε * μ.real Set.univ := by
  have hp : Integrable (Function.uncurry H) (μ.prod ν) :=
    ⟨hH.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun z => hK z.1 z.2)⟩
  have hs (y : ℝ) : Integrable (fun x => H x y) μ :=
    ⟨(hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => hK x y)⟩
  have h := two_giant_integral_transport
    (fun p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊ => primeResidueAtom q a p)
    (fun p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊ => primeResidueAtom q b p)
    (fun p => Real.log (p : ℕ)) (fun p => Real.log (p : ℕ)) μ ν H
    (fun p => primeResidueAtom_nonneg q b p) δ ε (fun p => hs (Real.log (p : ℕ)))
    hp.integral_prod_left (by intro p; simpa only [complexPrimeInterval_subtype] using hleft (Real.log (p : ℕ)))
    (Filter.Eventually.of_forall fun x => by simpa only [complexPrimeInterval_subtype] using hright x)
  simpa only [complexPrimeInterval_subtype, primeResidueAtom_subtype_mass] using h

theorem mixed_pair_integral_transport (q a b : ℕ) (u v r s G : ℝ)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (H : ℝ → ℝ → ℂ) (hH : Measurable (Function.uncurry H))
    (K : ℝ) (hK : ∀ x y, ‖H x y‖ ≤ K) (δ ε : ℝ)
    (hleft : ∀ y, ‖complexIntegerInterval q a u v G (fun x => H x y) - ∫ x, H x y ∂μ‖ ≤ δ)
    (hright : ∀ x, ‖complexPrimeInterval q b r s (H x) - ∫ y, H x y ∂ν‖ ≤ ε) :
    ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v G (fun x => H x y)) -
      ∫ x, ∫ y, H x y ∂ν ∂μ‖ ≤
      δ * reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + ε * μ.real Set.univ := by
  have hp : Integrable (Function.uncurry H) (μ.prod ν) :=
    ⟨hH.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun z => hK z.1 z.2)⟩
  have hs (y : ℝ) : Integrable (fun x => H x y) μ :=
    ⟨(hH.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x => hK x y)⟩
  have h := two_giant_integral_transport
    (fun p : Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊ => integerResidueAtom q a G p)
    (fun p : Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊ => primeResidueAtom q b p)
    (fun p => Real.log (p : ℕ)) (fun p => Real.log (p : ℕ)) μ ν H
    (fun p => primeResidueAtom_nonneg q b p) δ ε (fun p => hs (Real.log (p : ℕ)))
    hp.integral_prod_left (by intro p; simpa only [complexIntegerInterval_subtype] using hleft (Real.log (p : ℕ)))
    (Filter.Eventually.of_forall fun x => by simpa only [complexPrimeInterval_subtype] using hright x)
  simpa only [complexPrimeInterval_subtype, complexIntegerInterval_subtype,
    primeResidueAtom_subtype_mass] using h

end Ostmann

end OAI
