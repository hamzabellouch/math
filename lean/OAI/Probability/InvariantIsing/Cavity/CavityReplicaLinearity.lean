import OAI.Probability.InvariantIsing.Cavity.CavityFullSymmetry

namespace OAI

/-! Finite linear combinations of bounded replica tests commute with
the normalized Gibbs average, including a zero denominator. -/

noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_referenceReplicaMean_sum {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : Measure X) [SigmaFinite ν] (H : X → ℝ) {r : ℕ}
    (F : ι → (Fin r → X) → ℝ) (hF : ∀ i, Measurable (F i))
    (B : ι → ℝ) (hB : ∀ i σ, |F i σ| ≤ B i) :
    referenceReplicaMean ν H (fun σ => ∑ i, F i σ) =
      ∑ i, referenceReplicaMean ν H (F i) := by
  simp only [referenceReplicaMean_eq_ratio]
  by_cases hi : Integrable (fun σ : Fin r → X => Real.exp (∑ i, H (σ i)))
      (Measure.pi (fun _ => ν))
  · have hip (i : ι) : Integrable
        (fun σ : Fin r → X => Real.exp (∑ j, H (σ j)) * F i σ)
        (Measure.pi (fun _ => ν)) := by
      apply (hi.mul_const (B i)).mono'
        ((hi.aestronglyMeasurable.mul (hF i).aestronglyMeasurable))
      exact ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_left (hB i σ) (Real.exp_pos _).le
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => hip i), Finset.sum_div]
  · simp only [integral_undef hi, div_zero, Finset.sum_const_zero]

lemma cavity_nested_replica_sum {Ω Ω' X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : Measure X) [SigmaFinite ν] (H : Ω → Ω' → X → ℝ) {r : ℕ}
    (F : ι → (Fin r → X) → ℝ) (hmF : ∀ i, Measurable (F i))
    (hmeas : ∀ i, Measurable (fun z : Ω × Ω' => referenceReplicaMean ν (H z.1 z.2) (F i)))
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ i σ, |F i σ| ≤ B) :
    (∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i σ) ∂P ∂μ) =
      ∑ i, ∫ ω, ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P ∂μ := by
  have hiG (ω : Ω) (i : ι) :
      Integrable (fun g => referenceReplicaMean ν (H ω g) (F i)) P :=
    integrable_of_measurable_abs_le ((hmeas i).comp measurable_prodMk_left)
      (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i) (hmF i) hB (hF i))
  have he (ω : Ω) :
      (∫ g, referenceReplicaMean ν (H ω g) (fun σ => ∑ i, F i σ) ∂P) =
        ∑ i, ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P := by
    simp_rw [cavity_referenceReplicaMean_sum ν _ F hmF (fun _ => B) hF]
    exact integral_finsetSum _ (fun i _ => hiG ω i)
  have hiU (i : ι) : Integrable
      (fun ω => ∫ g, referenceReplicaMean ν (H ω g) (F i) ∂P) μ :=
    integrable_of_measurable_abs_le
      ((hmeas i).stronglyMeasurable.integral_prod_right'.measurable)
      (fun ω => abs_integral_le_const_of_bound ((hmeas i).comp measurable_prodMk_left)
        (fun g => referenceReplicaMean_abs_le ν (H ω g) (F i) (hmF i) hB (hF i)))
  simp_rw [he]
  exact integral_finsetSum _ (fun i _ => hiU i)

end InvariantIsing

end

end OAI
