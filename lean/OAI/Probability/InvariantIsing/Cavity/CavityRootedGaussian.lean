import OAI.Probability.InvariantIsing.Cavity.CavityRootedResidual

namespace OAI

/-! Averaging the unchanged common Gaussian root in the quadratic cavity law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_rooted_quadratic_gaussian {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (S₀ : Matrix (Fin d) (Fin d) ℝ) (hS₀ : S₀.PosSemidef)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef) :
    (cavityRootedResidualKernel n K (H n) ∘ₘ
      ((multivariateGaussian 0 S₀).prod
        (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _))).map
      (cavityRootedField n) =
      multivariateGaussian 0
        (((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) +
          ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
            cavityResolvent K (H n))) := by
  let J := (1 - H 0 * K)⁻¹
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) J
  let T := (∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
    cavityResolvent K (H n)
  let P : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n) :=
    noiseCascadeLaw _ n b (cavityGaussianMarks S)
  have hT : T.PosSemidef := (Matrix.posSemidef_sum Finset.univ (fun (i : Fin n) _ =>
    cavity_innovation_covariance_posSemidef K (H i) (H (i + 1)) (S i) (hS i)
      (b i) (hdet i) (hdet (i + 1)) (hΔ i) (hQ i))).add
        (cavity_tilt_covariance_posSemidef K (H n) hR hQR)
  have hJ : (J * S₀ * J.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS₀.mul_mul_conjTranspose_same J
  have hs (s : EuclideanSpace ℝ (Fin d)) :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) T).map (fun z => L s + z) =
        multivariateGaussian (L s) T := by
    simpa using cavity_multivariateGaussian_affine_image (1 : Matrix (Fin d) (Fin d) ℝ)
      T hT 0 (L s)
  have he : (cavityRootedResidualKernel n K (H n) ∘ₘ
      ((multivariateGaussian 0 S₀).prod P)).map (cavityRootedField n) =
      ((multivariateGaussian 0 S₀).prod (multivariateGaussian 0 T)).map
        (fun p => L p.1 + p.2) := by
    apply Measure.ext_of_lintegral
    intro F hF
    have hy := measurable_cavityRootedField (d := d) n
    have hfy : Measurable (fun x => F (cavityRootedField (d := d) n x)) := hF.comp hy
    have hfl : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        F (L p.1 + p.2)) := hF.comp (by fun_prop)
    rw [lintegral_map hF hy, Measure.lintegral_bind (Kernel.aemeasurable _) hfy.aemeasurable,
      lintegral_prod _ hfy.lintegral_kernel.aemeasurable,
      lintegral_map hF (by fun_prop), lintegral_prod _ hfl.aemeasurable]
    congr 1
    funext s
    simp_rw [cavity_rooted_kernel_test n K (H n) _ F hF]
    have hys : Measurable (fun x : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
        EuclideanSpace ℝ (Fin d) => cavityLeafSum n s x.1 + x.2) :=
      ((measurable_cavityLeafSum n s).comp measurable_fst).add measurable_snd
    have hfys : Measurable (fun x : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n ×
        EuclideanSpace ℝ (Fin d) => F (cavityLeafSum n s x.1 + x.2)) := hF.comp hys
    change (∫⁻ V, ∫⁻ x, F (cavityLeafSum n s x.1 + x.2)
      ∂cavityQuadraticResidualKernel n K (H n) s V ∂P) = _
    rw [← Measure.lintegral_bind (Kernel.aemeasurable _) hfys.aemeasurable,
      ← lintegral_map hF hys,
      cavity_quadratic_one_gaussian n K H S b hbCascade hK hH hS hb hdet hΔ hQ hR hQR s]
    change (∫⁻ z, F z ∂multivariateGaussian (L s) T) = _
    rw [← hs s, lintegral_map hF (by fun_prop)]
  rw [he]
  have hr : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).map L =
      multivariateGaussian 0 (J * S₀ * J.transpose) := by
    simpa only [map_zero, zero_add] using cavity_multivariateGaussian_affine_image J S₀ hS₀ 0 0
  have hp := Measure.map_prod_map (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀)
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) T) L.measurable measurable_id
  rw [hr, Measure.map_id] at hp
  rw [show (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => L p.1 + p.2) =
      (fun p => p.1 + p.2) ∘ Prod.map L id from rfl,
    ← Measure.map_map (by fun_prop) (L.measurable.prodMap measurable_id), ← hp,
    cavity_gaussian_add_law _ T hJ hT]

end InvariantIsing

end

end OAI
