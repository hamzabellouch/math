import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRankGram
import OAI.Probability.InvariantIsing.Cavity.CavityHaarCompression

namespace OAI

/-! Almost-sure positive definiteness of finite Haar spectral compressions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

/-- A Haar-rotated orthonormal `q`-frame has positive-definite compression
to every fixed coordinate window containing at least `q` rows. -/
theorem cavityHaarWindowGram_posDef {N q : ℕ} (l u : ℕ)
    (hlq : l + q ≤ u) (huN : u ≤ N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin N) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1) :
    ∀ᵐ (U : Orthogonal N) ∂μ, (cavityWindowGram ((U : Matrix (Fin N) (Fin N) ℝ) * A₀) l u).PosDef := by
  have hqN : q ≤ N := by omega
  have hlu : l ≤ u := by omega
  have hp : stdGaussian (EuclideanSpace ℝ (Fin N × Fin q)) (cavityArrayGood N q) ≠ 0 := by
    rw [cavityArrayGood_probability, cavityGoodGram_probability_one N q hqN]
    exact one_ne_zero
  have : IsProbabilityMeasure (cavityConditionedFrameLaw N q) :=
    cavityConditionedFrameLaw_probability hp
  have hdet : Measurable (fun A : Matrix (Fin N) (Fin q) ℝ =>
      (cavityWindowGram A l u).det) :=
    (continuous_cavityWindowGram N q l u).matrix_det.measurable
  have hs : MeasurableSet {A : Matrix (Fin N) (Fin q) ℝ |
      0 < (cavityWindowGram A l u).det} := measurableSet_lt measurable_const hdet
  have hraw : ∀ᵐ x ∂cond (cavityGaussianRows q) (cavityGoodGram q N),
      0 < (cavityWindowGram (cavityNormalizeFrame (cavityGaussianMatrix x N)) l u).det := by
    exact cond_absolutelyContinuous.ae_le
      ((cavityGaussianRows_normalized_window_posDef N q l u hlq huN).mono
        (fun _ hx => hx.det_pos))
  have hframe : ∀ᵐ A ∂cavityConditionedFrameLaw N q,
      0 < (cavityWindowGram A l u).det := by
    rw [← cavityConditionedFrameLaw_of_rows N q]
    exact (ae_map_iff (measurable_cavityGaussianNormalizedFrame q N).aemeasurable hs).mpr hraw
  rw [cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw N q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal N q) A₀ hA₀] at hframe
  have hm : Measurable (fun U : Orthogonal N =>
      (U : Matrix (Fin N) (Fin N) ℝ) * A₀) :=
    ((continuous_cavityFrameAction N q).comp
      (continuous_id.prodMk continuous_const)).measurable
  have he : ∀ᵐ (U : Orthogonal N) ∂μ,
      0 < (cavityWindowGram ((U : Matrix (Fin N) (Fin N) ℝ) * A₀) l u).det :=
    ae_of_ae_map hm.aemeasurable hframe
  filter_upwards [he] with U hU
  exact cavity_posDef_of_posSemidef_det_ne_zero
    (cavityWindowGram_posSemidef _ l u hlu) hU.ne'

end InvariantIsing

end

end OAI
