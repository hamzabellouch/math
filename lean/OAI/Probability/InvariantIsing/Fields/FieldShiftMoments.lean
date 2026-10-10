import OAI.Probability.InvariantIsing.Fields.FieldSmoothFamily
import OAI.Probability.InvariantIsing.Fields.FieldGaussianTiltMoments

namespace OAI

/-! Uniform polynomial moments for the actual shifted Gaussian weights
of the finite scalar field. The bound is independent of the spatial bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma FieldSmoothFamily.spatial_abs_sub_le {I : Set ℝ} (F : FieldSmoothFamily I)
    (t x y : ℝ) : |F.U (t, x) - F.U (t, y)| ≤ F.KX * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (F.spatial t z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using F.bX (t, z))
      convex_univ (mem_univ y) (mem_univ x)

lemma FieldSmoothFamily.shifted_second_moment {I : Set ℝ} (F : FieldSmoothFamily I)
    (t z r ζ R : ℝ) (hr : |r| ≤ R) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2)
      ((gaussianReal 0 1).tilted (fun u => ζ * F.U (t, z + r * u))) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2
        ∂(gaussianReal 0 1).tilted (fun u => ζ * F.U (t, z + r * u))) ≤
        fieldGaussianMomentCap (|ζ| * F.KX * R) := by
  let H : ℝ → ℝ := fun u => ζ * F.U (t, z + r * u)
  let U : ℝ → ℝ := fun u => H u - ζ * F.U (t, z)
  have hmH : Measurable H := (F.mU.comp (by fun_prop)).const_mul ζ
  have hmU : Measurable U := hmH.sub_const _
  have hb : ∀ u, |U u| ≤ (|ζ| * F.KX * R) * |u| := by
    intro u
    have hsp := F.spatial_abs_sub_le t (z + r * u) z
    have hdiff : z + r * u - z = r * u := by ring
    rw [hdiff, abs_mul] at hsp
    calc
      |U u| = |ζ| * |F.U (t, z + r * u) - F.U (t, z)| := by
        dsimp only [U, H]
        rw [← mul_sub, abs_mul]
      _ ≤ |ζ| * (F.KX * (|r| * |u|)) := mul_le_mul_of_nonneg_left hsp (abs_nonneg ζ)
      _ ≤ |ζ| * (F.KX * (R * |u|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hr (abs_nonneg u)) F.kx_nonneg) (abs_nonneg ζ)
      _ = _ := by ring
  have hExp : Integrable (fun u => Real.exp (H u)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
      (F.mU.comp (by fun_prop)) ((F.growth t).add_left z |>.scale_argument r) ζ
  have hprob : IsProbabilityMeasure ((gaussianReal 0 1).tilted H) :=
    isProbabilityMeasure_tilted hExp
  have he : (gaussianReal 0 1).tilted U = (gaussianReal 0 1).tilted H := by
    have hh := tilted_tilted hExp (fun _ => -(ζ * F.U (t, z)))
    simpa only [tilted_const, Pi.add_def, sub_eq_add_neg, U] using hh.symm
  have h := field_centered_tilt_second_moment hmU hb
  rwa [he] at h

end InvariantIsing

end

end OAI
