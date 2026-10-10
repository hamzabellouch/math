import OAI.Probability.InvariantIsing.Cavity.CavityGaussianCurveMean
import OAI.Probability.InvariantIsing.Gaussian.GaussianBaseComparison

namespace OAI

/-! The finite cavity comparison for cylinder fields. Independent copies
are realized by disjoint coordinate tags, preserving both endpoint laws. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma finite_cylinder_penalty_comparison {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H V : X → ℝ) (c : ℝ) (C A : X → ℕ →₀ ℝ)
    (hCA : ∀ x y, cylinderCross (C x) (A y) = 0)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  classical
  obtain ⟨n, hn⟩ := finite_family_support_bound (Sum.elim C A)
  have hC (x : X) : ∀ j ∈ (C x).support, j < n + 1 :=
    fun j hj => hn (Sum.inl x) j (Finsupp.mem_support_iff.mp hj)
  have hA (x : X) : ∀ j ∈ (A x).support, j < n + 1 :=
    fun j hj => hn (Sum.inr x) j (Finsupp.mem_support_iff.mp hj)
  let C' : X → Fin (n + 1) → ℝ := fun x i => C x i
  let A' : X → Fin (n + 1) → ℝ := fun x i => A x i
  let w := fun x => ν.real {x}
  have hw : GibbsReference w := finite_reference_GibbsReference ν
  have hca : ∀ x y, gaussianCross C' A' x y = 0 := by
    intro x y
    simp only [gaussianCross, C', A']
    rw [← cylinderCross_prefix (C x) (A y) (hC x)]
    exact hCA x y
  have hk : ∀ x y, |gaussianCross A' A' x y - gaussianCross C' C' x y| ≤
      c * (V x + V y) := by
    intro x y
    simp only [gaussianCross, C', A']
    rw [← cylinderCross_prefix (A x) (A y) (hA x),
      ← cylinderCross_prefix (C x) (C y) (hC x)]
    exact hK x y
  have he (D : X → ℝ) (Q : X → ℕ →₀ ℝ)
      (hQ : ∀ x j, j ∈ (Q x).support → j < n + 1) :
      (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (D x + cylinderField (Q x) g) ∂ν)
        ∂gaussianCoordinates) =
      ∫ g, Real.log (finitePartition w (fun x => D x +
        linearGaussian (fun (x : X) (i : Fin (n + 1)) => Q x i) g x))
          ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    have hp (g : ℕ → ℝ) : Real.log (∫ x, Real.exp (D x + cylinderField (Q x) g) ∂ν) =
        Real.log (finitePartition w (fun x => D x +
          linearGaussian (fun (x : X) (i : Fin (n + 1)) => Q x i) (fun i => g i) x)) := by
      rw [integral_fintype Integrable.of_finite]
      simp only [finitePartition, w, cylinderField_eq_prefix _ (hQ _)]
      rfl
    simp_rw [hp]
    exact (gaussian_prefix_measurePreserving (n + 1)).hasLaw.integral_comp
      (by simpa only [one_mul] using
        (continuous_log_finitePartition hw D (fun (x : X) (i : Fin (n + 1)) => Q x i) 1).aestronglyMeasurable)
  rw [he (fun x => H x - 2 * c * V x) C hC, he H A hA]
  exact cavity_finite_gaussian_penalty_comparison hw H V c C' A' hca hk

lemma cylinder_log_mean_tag {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) (H : X → ℝ)
    (A : X → ℕ →₀ ℝ) (j : ℕ) :
    (∫ g : ℕ → ℝ, Real.log (∫ x,
      Real.exp (H x + cylinderField (tagCoefficients j (A x)) g) ∂ν) ∂gaussianCoordinates) =
    ∫ g : ℕ → ℝ, Real.log (∫ x,
      Real.exp (H x + cylinderField (A x) g) ∂ν) ∂gaussianCoordinates := by
  have hm : Measurable (fun g : ℕ → ℝ => Real.log
      (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)) := by
    exact (((measurable_of_countable H).comp measurable_snd).add
      (measurable_cylinderFields A)).exp.stronglyMeasurable.integral_prod_right'.measurable.log
  simpa only [Function.comp_def, cylinderField_tag, gaussianCoordinates] using
    (gaussian_pullback_measurePreserving (Nat.pair j) (pair_left_injective j)).hasLaw.integral_comp
      hm.aestronglyMeasurable

/-- Only the two covariance kernels matter: disjoint Gaussian copies
automatically supply the zero mixed covariance required by interpolation. -/
theorem finite_cylinder_covariance_penalty_comparison {X : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H V : X → ℝ) (c : ℝ)
    (C A : X → ℕ →₀ ℝ)
    (hK : ∀ x y, |cylinderCross (A x) (A y) - cylinderCross (C x) (C y)| ≤
      c * (V x + V y)) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x - 2 * c * V x + cylinderField (C x) g) ∂ν)
      ∂gaussianCoordinates) ≤
    ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates := by
  have h := finite_cylinder_penalty_comparison ν H V c
    (fun x => tagCoefficients 0 (C x)) (fun x => tagCoefficients 1 (A x))
    (fun x y => by simp only [cylinderCross_tag, ite_false, zero_ne_one])
    (fun x y => by simpa only [cylinderCross_tag, ite_true] using hK x y)
  simpa only [cylinder_log_mean_tag] using h

end InvariantIsing

end

end OAI
