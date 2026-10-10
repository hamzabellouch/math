import OAI.Analysis.FreeEntropy.RandomMatrixConvergence

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology ENNReal
namespace FiniteEntropySeparation
 theorem heatMatrix_noiseBound {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) {R : ℝ}
    (hR : 0≤R) (hA : ∀i,matrixOpNorm (A i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ) (i : Fin n) :
    matrixOpNorm (heatMatrix A u x i) ≤ (1+Real.sqrt u)*jointNoiseBound R x := by
  have h1 := jointMatrix_norm_bound A hR hA x (Sum.inl i)
  have h2 := jointMatrix_norm_bound A hR hA x (Sum.inr i)
  have h := matrixOpNorm_add (A i) ((Real.sqrt u:ℂ) • gueMatrix x i)
  rw [matrixOpNorm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at h
  change matrixOpNorm (heatMatrix A u x i) ≤ _ at h
  calc
    _ ≤ matrixOpNorm (A i)+Real.sqrt u*matrixOpNorm (gueMatrix x i) := h
    _ ≤ jointNoiseBound R x+Real.sqrt u*jointNoiseBound R x := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
    _ = _ := by ring
 theorem heatMoment_bound {n d : ℕ} (hd : 0<d) (a : MatrixCoordinates n d) {R : ℝ}
    (hR : 0≤R) (ha : ∀i,matrixOpNorm (hermitianMatrix a i)≤R) (u : ℝ) (x : MatrixIndex n d → ℝ) (w : List (Fin n)) :
    ‖matrixMoment (heatCoordinates a u x) w‖ ≤ (1+Real.sqrt u)^w.length*jointNoiseBound R x^w.length := by
  rw [matrixMoment_heatCoordinates]
  apply (matrix_normalized_trace_bound hd _).trans
  rw [← mul_pow]
  exact matrixOpNorm_word _ _ (mul_nonneg (by positivity) (jointNoiseBound_nonneg hR x)) (fun i _ => heatMatrix_noiseBound _ hR ha u x i)
 theorem heatMoment_power_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) (m : ℕ) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z.1 u z.2) w‖^m)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  have hb := ((jointNoiseBound_moment (n := n) hd hR (w.length*m)).1.const_mul ((1+Real.sqrt u)^(w.length*m))).comp_snd μ
  apply hb.mono'
  · exact (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).norm.pow m).aestronglyMeasurable
  have hm : ∀ᵐ z ∂μ.prod (productGaussian (MatrixIndex n d)),∀i,matrixOpNorm (hermitianMatrix z.1 i)≤R := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · filter_upwards [hμ] with a ha
      exact ae_of_all _ (fun _ => ha)
    · simpa only [Set.ofPred_forall,Function.comp_apply] using MeasurableSet.iInter (fun i : Fin n => measurableSet_le ((matrixOpNorm_continuous.comp (hermitianMatrix_continuous (n := n) (d := d) i)).comp (continuous_fst : Continuous (Prod.fst : MatrixCoordinates n d × (MatrixIndex n d → ℝ) → MatrixCoordinates n d))).measurable (measurable_const (a := R)))
  filter_upwards [hm] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  simpa only [mul_pow,← pow_mul] using pow_le_pow_left₀ (norm_nonneg _) (heatMoment_bound hd z.1 hR hz u z.2 w) m
 theorem heatMoment_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => matrixMoment (heatCoordinates z.1 u z.2) w)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  apply integrable_norm_iff (((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).aestronglyMeasurable) |>.mp
  simpa using heatMoment_power_integrable hd μ hR hμ u w 1
 theorem heatMoment_error_integrable {n d : ℕ} (hd : 0<d) (μ : Measure (MatrixCoordinates n d)) [IsFiniteMeasure μ]
    {R : ℝ} (hR : 0≤R) (hμ : ∀ᵐ a ∂μ,∀i,matrixOpNorm (hermitianMatrix a i)≤R)
    (u : ℝ) (w : List (Fin n)) (c : ℂ) :
    Integrable (fun z : MatrixCoordinates n d × (MatrixIndex n d → ℝ) => ‖matrixMoment (heatCoordinates z.1 u z.2) w-c‖^2)
      (μ.prod (productGaussian (MatrixIndex n d))) := by
  have hi := ((heatMoment_power_integrable hd μ hR hμ u w 2).add (integrable_const (‖c‖^2))).const_mul 2
  apply hi.mono' (((((matrixMoment_continuous w).comp (heatCoordinates_continuous u)).sub continuous_const).norm.pow 2).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    dsimp only [Pi.add_apply,Pi.pow_apply,Pi.sub_apply,Function.comp_apply]
    have h := norm_sub_le (matrixMoment (heatCoordinates z.1 u z.2) w) c
    have hn := norm_nonneg (matrixMoment (heatCoordinates z.1 u z.2) w-c)
    nlinarith [sq_nonneg (‖matrixMoment (heatCoordinates z.1 u z.2) w‖-‖c‖)])
end FiniteEntropySeparation

end

end OAI
