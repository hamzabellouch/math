import OAI.Analysis.FreeEntropy.TensorHermite

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem measure_pi_mono {ι : Type u1} [Fintype ι] {α : ι → Type u2} [∀ i,MeasurableSpace (α i)]
    (μ ν : (i:ι) → Measure (α i)) [∀i,SigmaFinite (μ i)] (h : ∀i,μ i≤ν i) :
    Measure.pi μ ≤ Measure.pi ν := by
  have ho : (Measure.pi μ).toOuterMeasure ≤ OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s _
    change Measure.pi μ (Set.pi univ s) ≤ _
    rw [Measure.pi_pi]
    exact prod_le_prod (fun i _ => h i (s i))
  rw [Measure.le_iff]
  intro s hs
  conv_rhs => rw [Measure.pi, toMeasure_apply _ _ hs]
  exact ho s
 theorem gaussianPDF_le_one (x : ℝ) : gaussianPDF 0 1 x ≤ 1 := by
  rw [gaussianPDF]
  apply ENNReal.ofReal_le_one.mpr
  have hp : 1 ≤ Real.sqrt (2*Real.pi) := by nlinarith [Real.sq_sqrt (show 0≤2*Real.pi by positivity),Real.sqrt_nonneg (2*Real.pi),Real.pi_gt_three]
  have he : Real.exp (-(x-0)^2/(2:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x-0)])
  dsimp [gaussianPDFReal]
  norm_num only [NNReal.coe_one, mul_one]
  calc
    _ ≤ (Real.sqrt (2*Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ ≤ 1 := by rw [mul_one]; exact (inv_le_one₀ (by positivity)).2 hp
 theorem gaussianReal_le_volume : gaussianReal 0 1 ≤ (volume : Measure ℝ) := by
  rw [Measure.le_iff']
  intro s
  rw [gaussianReal_apply 0 one_ne_zero s]
  calc
    _ ≤ ∫⁻ _ : ℝ in s, (1:ℝ≥0∞) := lintegral_mono (fun x => gaussianPDF_le_one x)
    _ = volume s := by simp
 theorem productGaussian_le_volume (ι : Type u3) [Fintype ι] :
    productGaussian ι ≤ (volume : Measure (ι → ℝ)) :=
  measure_pi_mono _ _ (fun _ => gaussianReal_le_volume)
 theorem productGaussian_toLp_le_volume (ι : Type u4) [Fintype ι] (s : Set (EuclideanSpace ℝ ι)) :
    productGaussian ι (WithLp.toLp 2 ⁻¹' s) ≤ volume s := by
  apply (productGaussian_le_volume ι _).trans
  exact (PiLp.volume_preserving_toLp ι).measure_preimage_le s
end FiniteEntropySeparation

end

end OAI
