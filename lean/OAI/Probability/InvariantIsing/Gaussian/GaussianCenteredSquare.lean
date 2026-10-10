import OAI.Probability.InvariantIsing.Gaussian.GaussianSingularFluctuation
import OAI.Probability.InvariantIsing.Pressure.RandomSqrtLimit

namespace OAI

/-! Scaled centered Gaussian squares are uniformly integrable using variance alone. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace InvariantIsing

lemma finiteGaussian_centeredSquare_integrable {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : HasLaw Z (stdGaussian _) P) (r : ℝ) :
    Integrable (fun ω => (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r) P := by
  have h := (hZ.memLp_comp (finiteGaussian_lipschitz_memLp_two hf)).sub
    (memLp_const (∫ x, f x ∂stdGaussian _))
  exact h.integrable_sq.div_const r

lemma finiteGaussian_centeredSquare_L1_bound {ι : Type*} [Fintype ι]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : LipschitzWith 1 f)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ ι) (hZ : HasLaw Z (stdGaussian _) P)
    (r : ℝ) (hr : 0 < r) :
    eLpNorm (fun ω => (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r) 1 P ≤
      ENNReal.ofReal (1/r) := by
  have hi := finiteGaussian_centeredSquare_integrable hf P Z hZ r
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  have he : (∫ ω, ‖(f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r‖ ∂P) =
      variance f (stdGaussian _)/r := by
    have hn (ω) : ‖(f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r‖ =
        (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2/r :=
      Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hr.le)
    simp_rw [hn]
    rw [integral_div]
    have h := hZ.integral_comp (f := fun y => (f y-(∫ x, f x ∂stdGaussian _))^2)
      ((hf.continuous.sub continuous_const).pow 2).aestronglyMeasurable
    rw [show (∫ ω, (f (Z ω)-(∫ x, f x ∂stdGaussian _))^2 ∂P) =
        ∫ y, (f y-(∫ x, f x ∂stdGaussian _))^2 ∂stdGaussian _ from h]
    rw [← variance_eq_integral hf.continuous.aemeasurable]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ hr.le
  simpa only [NNReal.coe_one,one_pow] using finiteGaussian_lipschitz_variance hf

theorem gaussianCenteredSquare_uniformIntegrable {ι : ℕ → Type*} [∀ k, Fintype (ι k)]
    (f : (k : ℕ) → EuclideanSpace ℝ (ι k) → ℝ) (hf : ∀ k, LipschitzWith 1 (f k))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (k : ℕ) → Ω → EuclideanSpace ℝ (ι k))
    (hZ : ∀ k, HasLaw (Z k) (stdGaussian _) P) :
    UniformIntegrable (fun k ω =>
      (f k (Z k ω)-(∫ x, f k x ∂stdGaussian _))^2/(k+1)) 1 P := by
  have hi k := finiteGaussian_centeredSquare_integrable (hf k) P (Z k) (hZ k) (k+1)
  have hb k := finiteGaussian_centeredSquare_L1_bound (hf k) P (Z k) (hZ k) (k+1)
    (by positivity)
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (1/(k+1 : ℝ))) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using h
  refine ⟨unifIntegrable_of_tendsto_Lp_zero le_rfl (by simp)
    (fun k => memLp_one_iff_integrable.mpr (hi k)) (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ht (fun _ => zero_le) hb),1,?_⟩
  intro k
  apply (hb k).trans
  apply ENNReal.ofReal_le_one.mpr
  exact (div_le_one (by positivity : (0 : ℝ) < k+1)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)

end InvariantIsing

end

end OAI
