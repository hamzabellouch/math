import OAI.Probability.InvariantIsing.Arrays.DiagonalCovariance
import OAI.Probability.InvariantIsing.Arrays.PerturbationMeasurability

namespace OAI

/-! The Gaussian GG bound specialized to the manuscript's spectral/tree kernels. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma spectralMonomial_self_deviation_le {N m : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (q : Fin m → ℝ)
    (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) (σ : Spin N) :
    |(∏ a, projectedOverlap U (I a) σ σ ^ d a) - ∏ a, q a ^ d a| ≤
      ∑ a, (d a : ℝ) * |projectedOverlap U (I a) σ σ - q a| := by
  have hqa (a : Fin m) : |q a| ≤ 1 := by
    rw [abs_of_nonneg (hq a).1]
    exact (hq a).2
  have hp (a : Fin m) : |projectedOverlap U (I a) σ σ ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (projectedOverlap_abs_le_one _ _ _ _)
  have hqp (a : Fin m) : |q a ^ d a| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hqa a)
  exact (abs_prod_sub_prod_le_sum Finset.univ _ _ (fun a _ => hp a) (fun a _ => hqp a)).trans
    (Finset.sum_le_sum fun a _ => abs_pow_sub_pow_le_degree
      (projectedOverlap_abs_le_one _ _ _ _) (hqa a) (d a))

/-- The concrete Haar-dependent tensor coefficient map. -/
def spectralPerturbationCoefficients {Ω : Type*} {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (n r : ℕ) : Ω → (Spin N × LabeledLeaf n) → ℕ →₀ ℝ :=
  fun ω => jointSpectralMonomialCoefficients (specialRotation (U ω)) I d n r

def spectralPerturbationKernel {Ω : Type*} {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (n r : ℕ) (ω : Ω) (x y : Spin N × LabeledLeaf n) : ℝ :=
  (∏ a, projectedOverlap (specialRotation (U ω)) (I a) x.1 y.1 ^ d a) *
    treeOverlap n x.2 y.2 ^ r

lemma spectralPerturbationCoefficients_cross {Ω : Type*} {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (I : Fin m → Finset (Fin N))
    (d : Fin m → ℕ) (n r : ℕ) (ω : Ω) (x y : Spin N × LabeledLeaf n) :
    cylinderCross (spectralPerturbationCoefficients U I d n r ω x)
      (spectralPerturbationCoefficients U I d n r ω y) =
      spectralPerturbationKernel U I d n r ω x y :=
  jointSpectralMonomialCoefficients_cross (specialRotation (U ω)) I d n r x y

lemma measurable_spectralPerturbationFields {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : (Ω × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (spectralPerturbationCoefficients U I d n r p.1.1 p.2) p.1.2) := by
  apply measurable_from_prod_countable_left
  intro x
  have h := (measurable_jointSpectralMonomialField I d n r x).comp
    (hU.prodMap measurable_id)
  simpa only [spectralPerturbationCoefficients, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq] using h

lemma measurable_spectralPerturbationCross {Ω : Type*} [MeasurableSpace Ω] {N m : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : Ω × ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) =>
      cylinderCross (spectralPerturbationCoefficients U I d n r p.1 p.2.1)
        (spectralPerturbationCoefficients U I d n r p.1 p.2.2)) := by
  apply measurable_from_prod_countable_left
  intro xy
  simp only [spectralPerturbationCoefficients, jointSpectralMonomialCoefficients_cross]
  exact (Finset.measurable_prod Finset.univ (fun a _ =>
    ((measurable_projectedOverlap (I a) xy.1.1 xy.2.1).comp hU).pow_const (d a))).mul_const _

/-- Concrete conditional Gaussian GG estimate. The distribution of the external
rotation and the other disorder is arbitrary; Gaussian coordinates are the
independent product factor. -/
theorem spectralPerturbation_gg_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {N m n k : ℕ}
    (U : Ω → SpecialOrthogonal N) (hU : Measurable U)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (treeDegree : ℕ)
    {ν : Ω → Measure (Spin N × LabeledLeaf n)} (hν : Measurable ν)
    [∀ ω, IsProbabilityMeasure (ν ω)] (t b d₀ : ℝ)
    (D : Ω → (Fin (k + 1) → Spin N × LabeledLeaf n) → ℝ)
    (hDm : Measurable (Function.uncurry D)) {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ ω σ, |D ω σ| ≤ c)
    (hE : Integrable (fun z : Ω × (ℕ → ℝ) => ∫ x,
      |cylinderField (spectralPerturbationCoefficients U I d n treeDegree z.1 x) z.2 - b|
        ∂(ν z.1).tilted (fun x => t *
          cylinderField (spectralPerturbationCoefficients U I d n treeDegree z.1 x) z.2))
      (P.prod gaussianCoordinates)) :
    let A := spectralPerturbationCoefficients U I d n treeDegree
    let κ := spectralPerturbationKernel U I d n treeDegree
    |t| * |(k + 1 : ℕ) * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin (k + 1 + 1) → Spin N × LabeledLeaf n) =>
          D ω (Fin.tail τ) * κ ω ((Fin.tail τ) 0) (τ 0)) -
      randomCoefficientAverage P ν A t D * randomCoefficientAverage P ν A t
        (fun ω (τ : Fin 2 → Spin N × LabeledLeaf n) => κ ω (τ 1) (τ 0)) -
      randomCoefficientAverage P ν A t
        (fun ω σ => D ω σ * ∑ l : Fin k, κ ω (σ 0) (σ l.succ))| ≤
    2 * c * ((∫ z : Ω × (ℕ → ℝ), ∫ x, |cylinderField (A z.1 x) z.2 - b|
      ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
        ∂P.prod gaussianCoordinates) +
      |t| * (∫ z : Ω × (ℕ → ℝ), ∫ x, |κ z.1 x x - d₀|
        ∂(ν z.1).tilted (fun x => t * cylinderField (A z.1 x) z.2)
          ∂P.prod gaussianCoordinates)) := by
  let A := spectralPerturbationCoefficients U I d n treeDegree
  have hA (ω : Ω) (x : Spin N × LabeledLeaf n) :
      (A ω x).sum (fun _ c => c ^ 2) ≤ 1 :=
    jointSpectralMonomialCoefficients_variance_le_one (specialRotation (U ω)) I d n treeDegree x
  have hg := randomCoefficient_gaussian_gg_L1_bound (P := P) hν A
    (measurable_spectralPerturbationFields U hU I d n treeDegree)
    (measurable_spectralPerturbationCross U hU I d n treeDegree)
    hA t b d₀ D hDm hc hD hE
  simpa only [A, spectralPerturbationCoefficients_cross] using hg

end InvariantIsing

end

end OAI
