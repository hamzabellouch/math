import OAI.Probability.InvariantIsing.Cavity.CavityWeightedMoments

namespace OAI

/-! Polynomial extra-replica limits with a positive denominator or
logarithm regularizer. The unregularized weight may vanish. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_regularized_reciprocal_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (Z A : (n : ℕ) → Ω n → ℝ) (W D : Ω₀ → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hA : ∀ n, Measurable (A n))
    (hW : Measurable W) (hD : Measurable D) {b B δ : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B)
    (hZb : ∀ n ω, Z n ω ∈ Icc 0 b) (hWb : ∀ ω, W ω ∈ Icc 0 b)
    (hAb : ∀ n ω, |A n ω| ≤ B) (hDb : ∀ ω, |D ω| ≤ B)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ ω, A n ω * Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, D ω * W ω ^ k ∂Q))) (r : ℕ) :
    Tendsto (fun n => ∫ ω, A n ω / (Z n ω + δ) ^ r ∂P n) atTop
      (𝓝 (∫ ω, D ω / (W ω + δ) ^ r ∂Q)) := by
  have hc : ContinuousOn (fun z : ℝ => 1 / (z + δ) ^ r) (Icc 0 b) :=
    continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow r)
      (fun z hz => pow_ne_zero _ (by linarith [hz.1]))
  simpa only [one_div, ← div_eq_mul_inv] using
    cavity_weighted_moments_tendsto P Q Z A W D hZ hA hW hD hB hZb hWb hAb hDb hmom
      (fun z => 1 / (z + δ) ^ r) hc

theorem cavity_floored_log_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω₀) [IsProbabilityMeasure Q]
    (Z : (n : ℕ) → Ω n → ℝ) (W : Ω₀ → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : Measurable W) {b δ : ℝ} (hδ : 0 < δ)
    (hZb : ∀ n ω, Z n ω ∈ Icc 0 b) (hWb : ∀ ω, W ω ∈ Icc 0 b)
    (hmom : ∀ k : ℕ, Tendsto (fun n => ∫ ω, Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, W ω ^ k ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (Z n ω + δ) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (W ω + δ) ∂Q)) := by
  have hc : ContinuousOn (fun z : ℝ => Real.log (z + δ)) (Icc 0 b) :=
    (continuousOn_id.add continuousOn_const).log (fun z hz => by
      change z + δ ≠ 0
      linarith [hz.1])
  simpa only [one_mul] using cavity_weighted_moments_tendsto P Q Z (fun _ _ => 1) W
    (fun _ => 1) hZ (fun _ => measurable_const) hW measurable_const (B := 1) zero_le_one
    hZb hWb (fun _ _ => by norm_num) (fun _ => by norm_num)
    (fun k => by simpa only [one_mul] using hmom k) (fun z => Real.log (z + δ)) hc

end InvariantIsing

end

end OAI
