import OAI.Probability.SpanningForest.IndependentProcessVectors
import OAI.Probability.SpanningForest.JointInnovationLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem336.BrownianFamilyIdentification

variable {I : Type*}

def vectorGaussian (S : Finset I) (h : ℝ≥0) : Measure (EuclideanSpace ℝ S) :=
  (Measure.infinitePi (fun _ : S => gaussianReal 0 h)).map
    (MeasurableEquiv.toLp 2 (S → ℝ))

instance (S : Finset I) (h : ℝ≥0) : IsProbabilityMeasure (vectorGaussian S h) := by
  unfold vectorGaussian
  infer_instance

theorem charFun_vectorGaussian (S : Finset I) (h : ℝ≥0) (θ : EuclideanSpace ℝ S) :
    charFun (vectorGaussian S h) θ =
      Complex.exp (-((h : ℝ) : ℂ) * (‖θ‖ : ℂ) ^ 2 / 2) := by
  classical
  rw [vectorGaussian, Measure.infinitePi_eq_pi]
  change charFun ((Measure.pi (fun _ : S => gaussianReal 0 h)).map
    (WithLp.toLp 2)) θ = _
  rw [charFun_pi]
  simp only [charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [← Complex.exp_sum]
  congr 1
  rw [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq]
  simp [Complex.ofReal_sum, Finset.sum_div, Finset.mul_sum, neg_div, neg_mul]

variable {Ω Ω' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {Q : Measure Ω'} [IsProbabilityMeasure Q]

theorem identDistrib_brownian_family
    (F : Filtration ℝ≥0 mΩ)
    (W : I → ℝ≥0 → Ω → ℝ) (B : I → ℝ≥0 → Ω' → ℝ)
    (hW : ∀ i, Adapted F (W i)) (hBm : ∀ i t, Measurable (B i t))
    (hW0 : ∀ i, ∀ᵐ ω ∂P, W i 0 ω = 0)
    (hB : ∀ i, IsPreBrownianReal (B i) Q)
    (hi : iIndepFun (fun i ω t => B i t ω) Q)
    (hchar : ∀ (S : Finset I) (s t : ℝ≥0), s ≤ t →
      ∀ A : Set Ω, MeasurableSet[F s] A → ∀ θ : EuclideanSpace ℝ S,
      (∫ ω in A, Complex.exp ((inner ℝ
        (WithLp.toLp 2 (fun i : S => W i t ω - W i s ω) : EuclideanSpace ℝ S) θ : ℂ)
          * Complex.I) ∂P) = (P A).toReal • charFun (vectorGaussian S (t - s)) θ) :
    IdentDistrib (fun ω i t => W i t ω) (fun ω i t => B i t ω) P Q := by
  refine JointInnovationLaw.identDistrib_of_past_characteristic F W B hW hBm
    hW0 (fun i => (hB i).eval_zero_ae_eq_zero)
    (fun S s t => vectorGaussian S (t - s)) hchar ?_ ?_
  · intro S
    exact IndependentProcessVectors.hasIndepIncrements_vector hBm hi
      (fun i => (hB i).hasIndepIncrements) S
  · intro S s t hst
    have hstR : (s : ℝ) ≤ (t : ℝ) := hst
    have hd : nndist t.1 s.1 = t - s := by
      apply NNReal.coe_injective
      change dist (t : ℝ) (s : ℝ) = ((t - s : ℝ≥0) : ℝ)
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hstR), NNReal.coe_sub hst]
    simpa only [vectorGaussian, hd] using
      IndependentProcessVectors.brownian_vector_increment_hasLaw hBm hi hB S s t

end Problem336.BrownianFamilyIdentification

end

end OAI
