import OAI.Probability.InvariantIsing.Cavity.CavityProductDisorder

namespace OAI

/-! Product-disorder integration for normalized restricted weights and
the Gaussian/fresh-frame permutation used by the canonical cavity law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma cavity_product_disorder_weighted {Ω U X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure U) [IsProbabilityMeasure Q]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    {k r : ℕ} (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (w : (Ω × U) × (X × Spin k) → ℝ) (hw : Measurable w)
    (F : (Ω × U) × (Fin r → X × Spin k) → ℝ) (hF : Measurable F)
    {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    (∫ ω, ∫ u, cavityWeightedReplicaMean ((ν ω).prod π)
      (fun x => w ((ω,u),x)) (fun σ => F ((ω,u),σ)) ∂Q ∂P) =
    ∫ p, cavityWeightedReplicaMean ((ν p.1).prod π)
      (fun x => w (p,x)) (fun σ => F (p,σ)) ∂P.prod Q := by
  simpa only [cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using
    cavity_product_disorder_regularized P Q ν hν π w hw F hF hM hB (δ := 0) le_rfl hwb hFb

lemma integrable_cavity_bounded_weighted_mean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure X) (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (w : Ω × X → ℝ) (hw : Measurable w) {r : ℕ}
    (F : Ω × (Fin r → X) → ℝ) (hF : Measurable F) {M B : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hwb : ∀ ω x, w (ω,x) ∈ Icc 0 M) (hFb : ∀ ω σ, |F (ω,σ)| ≤ B) :
    Integrable (fun ω => cavityWeightedReplicaMean (ν ω) (fun x => w (ω,x))
      (fun σ => F (ω,σ))) P := by
  have hm := measurable_cavityRegularizedReplicaMean ν hν w hw F hF 0
  have hb ω := cavityRegularizedReplicaMean_abs_le (ν ω) (fun x => w (ω,x))
    (hw.comp measurable_prodMk_left) (fun σ => F (ω,σ)) (hF.comp measurable_prodMk_left)
    hM hB (δ := 0) le_rfl (hwb ω) (hFb ω)
  have hh := integrable_of_measurable_abs_le (μ := P) hm hb
  simpa only [cavityRegularizedReplicaMean,add_zero,cavityWeightedReplicaMean] using hh

lemma cavity_bounded_disorder_shuffle {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (R : Measure C) [IsProbabilityMeasure R]
    (f : (A × B) × C → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂(P.prod Q).prod R) = ∫ a, ∫ c, ∫ b, f ((a,b),c) ∂Q ∂ R ∂P := by
  have hi := integrable_of_measurable_abs_le (μ := (P.prod Q).prod R) hf hb
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  filter_upwards [] with a
  have hm : Measurable (fun p : B × C => f ((a,p.1),p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact integral_integral_swap (integrable_of_measurable_abs_le (μ := Q.prod R) hm
    (fun p => hb ((a,p.1),p.2)))

lemma cavity_bounded_disorder_dirac_shuffle {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (b : B)
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R) =
      ∫ a, ∫ d, ∫ c, f (((a,b),c),d) ∂Q ∂ R ∂P := by
  rw [cavity_bounded_disorder_shuffle (P.prod (Measure.dirac b)) Q R f hf hb,
    Measure.prod_dirac]
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  exact integral_map_of_stronglyMeasurable measurable_prodMk_right
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'

end InvariantIsing

end

end OAI
