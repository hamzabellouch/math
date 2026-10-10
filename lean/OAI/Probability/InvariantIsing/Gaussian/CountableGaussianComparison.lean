import OAI.Probability.InvariantIsing.Gaussian.GaussianMeanInterpolation
import OAI.Probability.InvariantIsing.Arrays.PerturbationMeasurability

namespace OAI

/-! Gaussian mean comparison for the actual countable spin/cascade-leaf prior. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators Topology NNReal

namespace InvariantIsing

lemma finite_cylinder_mean_increment_le {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (C A : X → ℕ →₀ ℝ) {K : ℝ}
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x + A x) g) ν 1 ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x) g) ν 1 ∂gaussianCoordinates| ≤ 2 * K := by
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
  have hk (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (x y : X) :
      |gaussianCross A' (affineGaussianCoefficients C' A' s) x y| ≤ K := by
    have hc := cylinderCross_prefix (A x) (C y + s • A y) (hA x)
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hc
    have hh := hK s hs x y
    rw [hc] at hh
    exact hh
  have he (s : ℝ) (g : ℕ → ℝ) :
      cgf (fun x => cylinderField (C x + s • A x) g) ν 1 =
        Real.log (finitePartition w (fun x => 0 +
          linearGaussian (affineGaussianCoefficients C' A' s)
            (fun i : Fin (n + 1) => g i) x)) := by
    unfold cgf mgf
    rw [integral_fintype Integrable.of_finite]
    simp only [one_mul, zero_add, finitePartition]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [cylinderField_add, cylinderField_smul,
      cylinderField_eq_prefix (C x) (hC x), cylinderField_eq_prefix (A x) (hA x),
      linearGaussian_affine]
    rfl
  have hm (s : ℝ) : (∫ g : ℕ → ℝ,
      cgf (fun x => cylinderField (C x + s • A x) g) ν 1 ∂gaussianCoordinates) =
      affineGaussianMean w (fun _ => 0) C' A' s := by
    simp_rw [he s]
    exact (gaussian_prefix_measurePreserving (n + 1)).hasLaw.integral_comp
      (by simpa only [one_mul] using
        (continuous_log_finitePartition hw (fun _ => 0) (affineGaussianCoefficients C' A' s) 1).aestronglyMeasurable)
  have hc := affineGaussianMean_abs_sub_le hw (fun _ => 0) C' A' hk
  rw [← hm 1, ← hm 0] at hc
  simpa only [one_smul, zero_smul, add_zero] using hc

lemma cylinder_cgf_restriction_mean_tendsto {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g)
      (normalizedRestriction ν (S n)) 1 ∂gaussianCoordinates) atTop
      (𝓝 (∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g) ν 1 ∂gaussianCoordinates)) := by
  have hv (x : X) : (((A x).sum (fun _ c => c ^ 2)).toNNReal : ℝ) ≤ B := by
    rw [Real.coe_toNNReal _ (show 0 ≤ (A x).sum (fun _ c => c ^ 2) from
      Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact hA x
  simpa only [cgf, mgf, one_mul] using
    gaussian_log_restriction_expectation_tendsto (measurable_cylinderFields A)
      (fun x => cylinderField_law (A x)) hv hS hExh hpos

/-- The finite Gaussian mean estimate passes to countable leaf priors.
The two endpoint variance caps ensure convergence of their actual means. -/
theorem countable_cylinder_mean_increment_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hCA : ∀ x, (C x + A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x + A x) g) ν 1 ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (C x) g) ν 1 ∂gaussianCoordinates| ≤ 2 * K := by
  obtain ⟨S, hS, hpos, hExh⟩ := countable_reference_exhaustion ν
  have hm₀ := cylinder_cgf_restriction_mean_tendsto ν C hC
    (fun n => (hS n).measurableSet) hExh hpos
  have hm₁ := cylinder_cgf_restriction_mean_tendsto ν (fun x => C x + A x) hCA
    (fun n => (hS n).measurableSet) hExh hpos
  apply le_of_tendsto ((hm₁.sub hm₀).abs)
  apply Filter.Eventually.of_forall
  intro n
  let := (hS n).fintype
  have : IsProbabilityMeasure (subtypeReference ν (S n)) :=
    subtypeReference_probability ν (hS n).measurableSet (hpos n)
  have hf := finite_cylinder_mean_increment_le (subtypeReference ν (S n))
    (fun x => C x) (fun x => A x) (fun s hs x y => hK s hs x y)
  have he (Q : X → ℕ →₀ ℝ) (g : ℕ → ℝ) :
      cgf (fun x : S n => cylinderField (Q x) g) (subtypeReference ν (S n)) 1 =
        cgf (fun x => cylinderField (Q x) g) (normalizedRestriction ν (S n)) 1 := by
    unfold cgf mgf
    congr 1
    exact (subtypeReference_preserving ν (hS n).measurableSet).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (1 * cylinderField (Q x) g))).aestronglyMeasurable
  have heplus (g : ℕ → ℝ) :
      cgf (fun x : S n => cylinderField (C x + A x) g) (subtypeReference ν (S n)) 1 =
        cgf (fun x => cylinderField (C x + A x) g) (normalizedRestriction ν (S n)) 1 :=
    he (fun x => C x + A x) g
  simpa only [heplus, he C] using hf

lemma cylinder_log_partition_mean_base {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B : ℝ} (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B) :
    (∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
      ∂gaussianCoordinates) = Real.log (∫ x, Real.exp (H x) ∂ν) +
      ∫ g : ℕ → ℝ, cgf (fun x => cylinderField (A x) g) (ν.tilted H) 1 ∂gaussianCoordinates := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  have he := cylinder_log_partition_base ν H hH A hA 1
  simp only [one_mul] at he
  rw [integral_congr_ae he, integral_add (integrable_const _)
    ((cylinder_cgf_memLp_two (ν.tilted H) A hA 1).integrable (by norm_num))]
  simp only [integral_const, probReal_univ, one_smul]

/-- The Gaussian mean comparison holds with the actual deterministic base
energy and any countable probability prior, including cascade-leaf weights. -/
theorem countable_cylinder_log_mean_increment_le {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (C A : X → ℕ →₀ ℝ) {B₀ B₁ K : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hCA : ∀ x, (C x + A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |cylinderCross (A x) (C y + s • A y)| ≤ K) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x + A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * K := by
  have : IsProbabilityMeasure (ν.tilted H) := isProbabilityMeasure_tilted hH
  rw [cylinder_log_partition_mean_base ν H hH (fun x => C x + A x) hCA,
    cylinder_log_partition_mean_base ν H hH C hC, add_sub_add_left_eq_sub]
  exact countable_cylinder_mean_increment_le (ν.tilted H) C A hC hCA hK

lemma cylinderCross_add_right (a b c : ℕ →₀ ℝ) :
    cylinderCross a (b + c) = cylinderCross a b + cylinderCross a c := by
  unfold cylinderCross
  simp only [Finsupp.add_apply, mul_add, Finsupp.sum]
  exact Finset.sum_add_distrib

/-- Endpoint mixed-cross bounds control the whole coefficient segment. -/
lemma cylinderCross_segment_bound {X : Type*} (A C : X → ℕ →₀ ℝ) {L : ℝ}
    (h₀ : ∀ x y, |cylinderCross (A x - C x) (C y)| ≤ L)
    (h₁ : ∀ x y, |cylinderCross (A x - C x) (A y)| ≤ L)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (x y : X) :
    |cylinderCross (A x - C x) (C y + s • (A y - C y))| ≤ L := by
  have he : C y + s • (A y - C y) = (1 - s) • C y + s • A y := by
    ext i
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    ring
  rw [he, cylinderCross_add_right, cylinderCross_smul_right, cylinderCross_smul_right]
  calc
    _ ≤ |(1 - s) * cylinderCross (A x - C x) (C y)| +
        |s * cylinderCross (A x - C x) (A y)| := abs_add_le _ _
    _ = (1 - s) * |cylinderCross (A x - C x) (C y)| +
        s * |cylinderCross (A x - C x) (A y)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hs.2), abs_of_nonneg hs.1]
    _ ≤ (1 - s) * L + s * L := add_le_add
      (mul_le_mul_of_nonneg_left (h₀ x y) (sub_nonneg.mpr hs.2))
      (mul_le_mul_of_nonneg_left (h₁ x y) hs.1)
    _ = L := by ring

/-- The form used for rotation comparison: any two bounded-variance
coefficient families on the actual countable prior can be compared from
mixed cross-covariances of their increment with the two endpoints. -/
theorem countable_cylinder_log_mean_compare {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    (H : X → ℝ) (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A C : X → ℕ →₀ ℝ) {B₀ B₁ L : ℝ}
    (hC : ∀ x, (C x).sum (fun _ c => c ^ 2) ≤ B₀)
    (hA : ∀ x, (A x).sum (fun _ c => c ^ 2) ≤ B₁)
    (h₀ : ∀ x y, |cylinderCross (A x - C x) (C y)| ≤ L)
    (h₁ : ∀ x y, |cylinderCross (A x - C x) (A y)| ≤ L) :
    |(∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (A x) g) ∂ν)
        ∂gaussianCoordinates) -
      ∫ g : ℕ → ℝ, Real.log (∫ x, Real.exp (H x + cylinderField (C x) g) ∂ν)
        ∂gaussianCoordinates| ≤ 2 * L := by
  have he (x : X) : C x + (A x - C x) = A x := by abel
  have h := countable_cylinder_log_mean_increment_le ν H hH C (fun x => A x - C x)
    hC (fun x => by simpa only [he] using hA x)
    (fun s hs x y => cylinderCross_segment_bound A C h₀ h₁ hs x y)
  simpa only [he] using h

end InvariantIsing

end

end OAI
