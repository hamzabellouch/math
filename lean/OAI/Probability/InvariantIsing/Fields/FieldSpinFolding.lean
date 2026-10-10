import OAI.Probability.InvariantIsing.Fields.FieldGaussianTransformLaw

namespace OAI

/-! Exact odd-observable law for an even Gaussian tilt. This is the
conditional-spin kernel in the radial field comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma field_abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := by
  rw [Real.tanh_eq, abs_div, abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
  apply (div_le_one (add_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  exact abs_sub_le_iff.mpr ⟨by linarith [Real.exp_pos (-x)], by linarith [Real.exp_pos x]⟩

lemma field_gaussian_odd_folded_integral (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Function.Even F) (ha : Function.Odd a)
    (hi : Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v)) :
    (∫ u, Real.exp (ζ * F u) * a u ∂gaussianReal z v) =
      (2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * v))) *
        ∫ u in Ici (0 : ℝ), (a u * Real.tanh ((z / v) * u)) * fieldFoldedWeight v ζ F z u := by
  let C := 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-z ^ 2 / (2 * (v : ℝ)))
  let g := fun u => gaussianPDFReal z v u * (Real.exp (ζ * F u) * a u)
  have hg : Integrable g volume := field_gaussian_density_integrable v hv z _ hi
  rw [integral_gaussianReal_eq_integral_smul hv]
  change (∫ u, g u) = _
  rw [field_integral_fold g hg, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ici
  intro u _hu
  dsimp only [g]
  rw [hF u, ha u]
  have he := field_gaussian_pair_sign v hv z u
  have hp := field_gaussian_pair_sum v hv z u
  calc
    _ = (gaussianPDFReal z v u - gaussianPDFReal z v (-u)) *
        (Real.exp (ζ * F u) * a u) := by ring
    _ = _ := by rw [he, hp]; dsimp only [C, fieldFoldedWeight]; ring

/-- The physical odd conditional spin observable equals the folded
observable multiplied by the exact conditional sign. -/
theorem field_gaussian_tilt_odd_integral_eq_folded (v : ℝ≥0) (hv : v ≠ 0) (z ζ : ℝ)
    (F a : ℝ → ℝ) (hF : Function.Even F) (ha : Function.Odd a)
    (hi : Integrable (fun u => Real.exp (ζ * F u) * a u) (gaussianReal z v))
    (hweight : Integrable (fun u => Real.exp (ζ * F u)) (gaussianReal z v)) :
    (∫ u, a u ∂(gaussianReal z v).tilted (fun u => ζ * F u)) =
      (∫ u in Ici (0 : ℝ), (a u * Real.tanh ((z / v) * u)) * fieldFoldedWeight v ζ F z u) /
        (∫ u in Ici (0 : ℝ), fieldFoldedWeight v ζ F z u) := by
  rw [integral_tilted_eq_div]
  have hn := field_gaussian_odd_folded_integral v hv z ζ F a hF ha hi
  have hd := field_gaussian_folded_integral v hv z ζ F (fun _ => 1) hF
    (by simpa only [mul_one] using hweight)
  simp only [mul_one, one_mul] at hd
  rw [hn, hd, mul_div_mul_left _ _ (field_folded_constant_pos v hv z).ne']

end InvariantIsing

end

end OAI
