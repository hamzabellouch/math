import OAI.Probability.InvariantIsing.Cavity.CavityFiniteTest
import OAI.Probability.InvariantIsing.Cavity.CavityTestExhaustion

namespace OAI

/-! Covariance comparison of bounded Gibbs tests on a countable prior,
proved by finite leaf exhaustion. The estimate is uniform in the cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_countable_test_comparison {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H J F : X → ℝ) {M₀ M₁ B₀ B₁ K E B s : ℝ}
    (hH : ∀ x, |H x| ≤ M₀) (hJ : ∀ x, |J x| ≤ M₁)
    (C A : X → ℕ →₀ ℝ)
    (hC : ∀ x, (C x).sum (fun _ z => z ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B₁) (hK : 0 ≤ K)
    (hcov : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤ K)
    (hbase : ∀ x, |H x - J x| ≤ E) (hB : 0 ≤ B) (hF : ∀ x, |F x| ≤ B) (hs : 0 < s) :
    |(∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (C x) g)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => J x + cylinderField (A x) g)
        ∂gaussianCoordinates| ≤
      (2 * (2 * K + E)) / s + B ^ 2 * s / 2 := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hmC := cavity_cylinder_test_restriction_mean_tendsto ν H F
    (cavity_bounded_base_exp_integrable ν H hH) C hC hF hS hExh hpos
  have hmA := cavity_cylinder_test_restriction_mean_tendsto ν J F
    (cavity_bounded_base_exp_integrable ν J hJ) A hA hF hS hExh hpos
  apply le_of_tendsto ((hmC.sub hmA).abs)
  apply Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := cavity_finite_test_comparison (subtypeReference ν (S n))
    (fun x => H x) (fun x => J x) (fun x => F x) (fun x => hH x) (fun x => hJ x)
    (fun x => C x) (fun x => A x) (fun x => hC x) (fun x => hA x) hK
    (fun x y => hcov x y) (fun x => hbase x) hB (fun x => hF x) hs
  have heC (g : ℕ → ℝ) := cavity_subtype_tilted_integral ν (hS n).measurableSet
    (fun x => H x + cylinderField (C x) g) F
  have heA (g : ℕ → ℝ) := cavity_subtype_tilted_integral ν (hS n).measurableSet
    (fun x => J x + cylinderField (A x) g) F
  simp_rw [heC, heA] at hf
  exact hf

end InvariantIsing

end

end OAI
