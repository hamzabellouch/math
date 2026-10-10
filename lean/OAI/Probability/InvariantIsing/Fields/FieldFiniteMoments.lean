import OAI.Probability.InvariantIsing.Fields.FieldFiniteShiftBounds
import OAI.Probability.InvariantIsing.Fields.FieldAffineMoments

namespace OAI

/-! Uniform Gaussian tilted moments for the finite height family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

lemma FieldFiniteFamily.spatial_abs_sub_le {n : ℕ} {I : Set (Fin n → ℝ)}
    (F : FieldFiniteFamily n I) (t : Fin n → ℝ) (ht : t ∈ I) (x y : ℝ) : |F.U (t, x) - F.U (t, y)| ≤ F.KX * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (univ : Set ℝ)) => (F.spatial_derivative t ht z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using F.bX (t, z) ht)
      convex_univ (mem_univ y) (mem_univ x)

lemma FieldFiniteFamily.shifted_second_moment {n : ℕ} {I : Set (Fin n → ℝ)}
    (F : FieldFiniteFamily n I) (t : Fin n → ℝ) (ht : t ∈ I) (z r ζ R : ℝ) (hr : |r| ≤ R) :
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
    have hsp := F.spatial_abs_sub_le t ht (z + r * u) z
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
      (F.mU.comp (by fun_prop)) ((F.growth t ht).add_left z |>.scale_argument r) ζ
  have hprob : IsProbabilityMeasure ((gaussianReal 0 1).tilted H) :=
    isProbabilityMeasure_tilted hExp
  have he : (gaussianReal 0 1).tilted U = (gaussianReal 0 1).tilted H := by
    have hh := tilted_tilted hExp (fun _ => -(ζ * F.U (t, z)))
    simpa only [tilted_const, Pi.add_def, sub_eq_add_neg, U] using hh.symm
  have h := field_centered_tilt_second_moment hmU hb
  rwa [he] at h


namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def affineShift (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) (u : ℝ) : ℝ :=
  F.U (F.shiftPoint a v u p)

def affineDifferential (a : ℝ) (v : Fin n → ℝ) (p : FieldCovariate n) (u : ℝ) :
    FieldCovariate n →L[ℝ] ℝ :=
  fieldFiniteLinear (fun i => F.shiftedTangent a v i u p) (F.shiftedMean a v u p)

def affineLaw (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : Measure ℝ :=
  (gaussianReal 0 1).tilted (fun u => ζ * F.affineShift a v p u)

lemma affineLaw_probability (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    IsProbabilityMeasure (F.affineLaw a v ζ p) := by
  apply isProbabilityMeasure_tilted
  exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments 0 1)
    (F.mU.comp (by fun_prop)) ((F.growth p.1 hp).add_left p.2 |>.scale_argument
      (Real.sqrt (fieldFiniteVariance a v p.1))) ζ

lemma affineLaw_quadratic_moment (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    Integrable (fun u : ℝ => (1 + |u|) ^ 2) (F.affineLaw a v ζ p) ∧
      (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤
        fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt (fieldFiniteVariance a v p.1)) := by
  simpa only [affineLaw, affineShift, shiftPoint, abs_of_nonneg (Real.sqrt_nonneg _)] using
    F.shifted_second_moment p.1 hp p.2 (Real.sqrt (fieldFiniteVariance a v p.1)) ζ
      (Real.sqrt (fieldFiniteVariance a v p.1)) (by rw [abs_of_nonneg (Real.sqrt_nonneg _)])

def affineMomentCap (ζ V : ℝ) : ℝ :=
  1 + |fieldGaussianMomentCap (|ζ| * F.KX * Real.sqrt V)|

lemma affineMomentCap_pos (ζ V : ℝ) : 0 < F.affineMomentCap ζ V := by
  unfold affineMomentCap
  positivity

lemma affineLaw_moment_le (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ}
    (hV : fieldFiniteVariance a v p.1 ≤ V) :
    (∫ u : ℝ, (1 + |u|) ^ 2 ∂F.affineLaw a v ζ p) ≤ F.affineMomentCap ζ V := by
  have h := F.shifted_second_moment p.1 hp p.2 (Real.sqrt (fieldFiniteVariance a v p.1)) ζ
    (Real.sqrt V) (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using Real.sqrt_le_sqrt hV)
  exact h.2.trans ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one))

lemma affineLaw_integral_bound (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {V : ℝ}
    (hV : fieldFiniteVariance a v p.1 ≤ V) {A : ℝ → ℝ} (hA : Measurable A)
    {C : ℝ} (hC : 0 ≤ C) (hB : ∀ u, |A u| ≤ C * (1 + |u|) ^ 2) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V :=
  (field_integral_abs_le_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ hp).1
    hA C hB).trans (mul_le_mul_of_nonneg_left (F.affineLaw_moment_le a v ζ hp hV) hC)

lemma affineLaw_linear_integrable (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) : Integrable A (F.affineLaw a v ζ p) := by
  apply field_integrable_of_quadratic_bound _ (F.affineLaw_quadratic_moment a v ζ hp).1 hA C
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

lemma affineLaw_bounded_integrable (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I)
    {A : ℝ → ℝ} (hA : Measurable A) (C : ℝ) (hB : ∀ u, |A u| ≤ C) :
    Integrable A (F.affineLaw a v ζ p) := by
  have := F.affineLaw_probability a v ζ hp
  exact Integrable.of_bound hA.aestronglyMeasurable C
    (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hB u)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
