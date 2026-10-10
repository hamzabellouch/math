import OAI.Probability.InvariantIsing.Cavity.CavityRegularizedKernel
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSpinModel

namespace OAI

/-! Fubini for the retained disorder and independent fresh rotations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma cavity_product_disorder_numerator {Ω U X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure U) [IsProbabilityMeasure Q]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {k r : ℕ} (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (w : (Ω × U) × (X × Spin k) → ℝ) (hw : Measurable w)
    (F : (Ω × U) × (Fin r → X × Spin k) → ℝ) (hF : Measurable F)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    (∫ ω, ∫ u, cavityWeightNumerator ((ν ω).prod π)
      (fun x => w ((ω,u),x)) (fun σ => F ((ω,u),σ)) ∂Q ∂P) =
    ∫ p, cavityWeightNumerator ((ν p.1).prod π)
      (fun x => w (p,x)) (fun σ => F (p,σ)) ∂P.prod Q := by
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν π
  have hm := measurable_cavityWeightNumerator (fun p => κ p) κ.measurable w hw F hF
  have hb p : |cavityWeightNumerator (κ p) (fun x => w (p,x))
      (fun σ => F (p,σ))| ≤ B * M^r :=
    cavityWeightNumerator_abs_le (κ p) _ _ hM hB
      (fun x => by rw [abs_of_nonneg (hwb p x).1]; exact (hwb p x).2) (hFb p)
  have hi := Integrable.of_bound (μ := P.prod Q) hm.aestronglyMeasurable
    (B * M^r) (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  simpa only [κ,cavityHaarSpinPriorKernel_apply] using (integral_prod _ hi).symm

lemma cavity_product_disorder_regularized {Ω U X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure U) [IsProbabilityMeasure Q]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {k r : ℕ} (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (w : (Ω × U) × (X × Spin k) → ℝ) (hw : Measurable w)
    (F : (Ω × U) × (Fin r → X × Spin k) → ℝ) (hF : Measurable F)
    {M B δ : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    (∫ ω, ∫ u, cavityRegularizedReplicaMean ((ν ω).prod π)
      (fun x => w ((ω,u),x)) (fun σ => F ((ω,u),σ)) δ ∂Q ∂P) =
    ∫ p, cavityRegularizedReplicaMean ((ν p.1).prod π)
      (fun x => w (p,x)) (fun σ => F (p,σ)) δ ∂P.prod Q := by
  let κ := cavityHaarSpinPriorKernel (U := U) ν hν π
  have hm := measurable_cavityRegularizedReplicaMean (fun p => κ p) κ.measurable w hw F hF δ
  have hb p : |cavityRegularizedReplicaMean (κ p) (fun x => w (p,x))
      (fun σ => F (p,σ)) δ| ≤ B :=
    cavityRegularizedReplicaMean_abs_le (κ p) _ (hw.comp measurable_prodMk_left)
      _ (hF.comp measurable_prodMk_left) hM hB hδ (hwb p) (hFb p)
  have hi := Integrable.of_bound (μ := P.prod Q) hm.aestronglyMeasurable
    B (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hb p)
  simpa only [κ,cavityHaarSpinPriorKernel_apply] using (integral_prod _ hi).symm

end InvariantIsing

end

end OAI
