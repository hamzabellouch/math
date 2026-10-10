import OAI.Geometry.Immersion.ClosedSurface.MetricTensors

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean

lemma base_decomposition (v : Base) : v = v.1 • dx + v.2 • dy := by
  ext <;> simp [dx, dy]

lemma derivative_base_decomposition {n : ℕ} (F : RField n) (p v : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  unfold coordDeriv
  conv_lhs => rw [base_decomposition v]
  simp only [map_add, map_smul]

lemma evaluate_realMetricTensor {n : ℕ} (F : RField n) (p v w : Base) :
    evaluate (realMetricTensor F p) v w = realMetric F v w p := by
  rw [realMetric, derivative_base_decomposition F p v, derivative_base_decomposition F p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realMetricTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realMetric]
  rw [dotProduct_comm (coordDeriv dy F p) (coordDeriv dx F p)]
  ring

lemma evaluate_realLinearizedTensor {n : ℕ} (F X : RField n) (p v w : Base) :
    evaluate (realLinearizedTensor F X p) v w = realLinearized F X v w p := by
  simp only [realLinearized, derivative_base_decomposition F p v,
    derivative_base_decomposition F p w, derivative_base_decomposition X p v,
    derivative_base_decomposition X p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realLinearizedTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realLinearized]
  ring



lemma realMetricTensor_comp {n : ℕ} {F : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hχ : DifferentiableAt ℝ χ p) :
    realMetricTensor (F ∘ χ) p = pullbackField χ p (realMetricTensor F (χ p)) := by
  ext i
  rw [realMetricTensor_apply]
  change realMetric (F ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realMetricTensor F (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realMetricTensor]
  simp only [realMetric, coordDeriv, fderiv_comp p hF hχ, ContinuousLinearMap.comp_apply]

lemma realLinearizedTensor_comp {n : ℕ} {F X : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hX : DifferentiableAt ℝ X (χ p))
    (hχ : DifferentiableAt ℝ χ p) :
    realLinearizedTensor (F ∘ χ) (X ∘ χ) p =
      pullbackField χ p (realLinearizedTensor F X (χ p)) := by
  ext i
  rw [realLinearizedTensor_apply]
  change realLinearized (F ∘ χ) (X ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realLinearizedTensor F X (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realLinearizedTensor]
  simp only [realLinearized, coordDeriv, fderiv_comp p hF hχ, fderiv_comp p hX hχ,
    ContinuousLinearMap.comp_apply]

lemma realOsc_comp {n : ℕ} (τ : ℝ) (Z : Field n) (χ : Base → Base) :
    realOsc τ Z ∘ χ = QuadraticMean.displacement τ (fun p => (χ p).1) (Z ∘ χ) := by
  funext p
  rw [realOsc_eq_displacement]
  rfl




lemma realLinearized_residual_comp {n : ℕ} {F X : RField n} {χ : Base → Base}
    (H : Base → PhaseMean.Tensor) {p : Base} (hF : DifferentiableAt ℝ F (χ p))
    (hX : DifferentiableAt ℝ X (χ p)) (hχ : DifferentiableAt ℝ χ p) :
    realLinearizedTensor (F ∘ χ) (X ∘ χ) p - pullbackField χ p (H (χ p)) =
      pullbackField χ p (realLinearizedTensor F X (χ p) - H (χ p)) := by
  rw [realLinearizedTensor_comp hF hX hχ, map_sub]

end ClosedSurfaceR4.RealModes

end

end OAI
