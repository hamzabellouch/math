import OAI.Probability.InvariantIsing.Cavity.CavityUniformComparison
import OAI.Probability.IsingPerceptron.BoundedTiltAverage

namespace OAI

/-! Bounded Gibbs tests pass from finite leaf restrictions to the full
countable reference. Only almost-everywhere partition integrability is
needed for the full Gaussian field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_subtype_tilted_integral {X : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] (ν : Measure X) [IsProbabilityMeasure ν]
    {S : Set X} (hS : MeasurableSet S) (H F : X → ℝ) :
    (∫ x : S, F x ∂(subtypeReference ν S).tilted (fun x => H x)) =
      ∫ x, F x ∂(normalizedRestriction ν S).tilted H := by
  rw [integral_tilted_eq_div, integral_tilted_eq_div]
  congr 1
  · exact (subtypeReference_preserving ν hS).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (H x) * F x)).aestronglyMeasurable
  · exact (subtypeReference_preserving ν hS).hasLaw.integral_comp
      (measurable_of_countable (fun x => Real.exp (H x))).aestronglyMeasurable

lemma cavity_tilted_test_norm_le {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H F : X → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) : ‖∫ x, F x ∂ν.tilted H‖ ≤ K := by
  have hb := norm_integral_le_of_norm_le_const (μ := ν.tilted H) (f := F)
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hF x))
  exact hb.trans (mul_le_of_le_one_right hK measureReal_le_one)

lemma cavity_tilted_test_restriction_tendsto {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H F : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν) {K : ℝ} (hF : ∀ x, |F x| ≤ K)
    {S : ℕ → Set X} (hS : ∀ n, MeasurableSet (S n))
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) :
    Tendsto (fun n => ∫ x, F x ∂(normalizedRestriction ν (S n)).tilted H) atTop
      (𝓝 (∫ x, F x ∂ν.tilted H)) := by
  have hnum : Integrable (fun x => Real.exp (H x) * F x) ν := by
    apply (hH.mul_const K).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hF x) (Real.exp_pos _).le
  have hz : (∫ x, Real.exp (H x) ∂ν) ≠ 0 := (integral_exp_pos hH).ne'
  simp only [integral_tilted_eq_div]
  exact normalized_restriction_gibbs_tendsto hS hExh hH hnum hz

theorem cavity_cylinder_test_restriction_mean_tendsto {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H F : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (A : X → ℕ →₀ ℝ) {B K : ℝ} (hA : ∀ x, (A x).sum (fun _ z => z ^ 2) ≤ B)
    (hF : ∀ x, |F x| ≤ K) {S : ℕ → Set X} (hS : ∀ n, (S n).Finite)
    (hExh : ∀ x, ∀ᶠ n in atTop, x ∈ S n) (hpos : ∀ n, ν (S n) ≠ 0) :
    Tendsto (fun n => ∫ g : ℕ → ℝ, ∫ x, F x
      ∂(normalizedRestriction ν (S n)).tilted (fun x => H x + cylinderField (A x) g)
        ∂gaussianCoordinates) atTop
      (𝓝 (∫ g : ℕ → ℝ, ∫ x, F x ∂ν.tilted (fun x => H x + cylinderField (A x) g)
        ∂gaussianCoordinates)) := by
  let νn := fun n => normalizedRestriction ν (S n)
  have : ∀ n, IsProbabilityMeasure (νn n) := fun n => normalizedRestriction_probability (hpos n)
  let G := fun (g : ℕ → ℝ) (x : X) => H x + cylinderField (A x) g
  have hG : Measurable (Function.uncurry G) := ((measurable_of_countable H).comp measurable_snd).add
    (measurable_cylinderFields A)
  have hm (n : ℕ) : Measurable (fun g : ℕ → ℝ => ∫ x, F x ∂(νn n).tilted (G g)) :=
    measurable_random_tilted_integral (ν := fun _ : ℕ → ℝ => νn n)
      (H := Function.uncurry G) (F := fun z : (ℕ → ℝ) × X => F z.2) measurable_const hG
      ((measurable_of_countable F).comp measurable_snd)
  apply tendsto_integral_of_dominated_convergence
    (μ := gaussianCoordinates)
    (F := fun n g => ∫ x, F x ∂(νn n).tilted (G g))
    (f := fun g => ∫ x, F x ∂ν.tilted (G g)) (fun _ : ℕ → ℝ => max K 0)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const (max K 0))
  · intro n
    exact ae_of_all _ (fun g => cavity_tilted_test_norm_le (νn n) (G g) F
      (le_max_right K 0) (fun x => (hF x).trans (le_max_left K 0)))
  · filter_upwards [cylinder_partition_exp_integrable_ae ν H hH A hA] with g hg
    exact cavity_tilted_test_restriction_tendsto ν (G g) F hg hF
      (fun n => (hS n).measurableSet) hExh

end InvariantIsing

end

end OAI
