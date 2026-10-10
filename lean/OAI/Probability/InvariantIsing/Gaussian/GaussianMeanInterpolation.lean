import OAI.Probability.InvariantIsing.Gaussian.BaseGaussianVariance

namespace OAI

/-! Finite Gaussian mean interpolation with arbitrary base energy and weights. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

def affineGaussianCoefficients {d : ℕ} (C A : X → Fin d → ℝ) (s : ℝ) : X → Fin d → ℝ :=
  fun x i => C x i + s * A x i

omit [Fintype X] in
lemma linearGaussian_affine {d : ℕ} (C A : X → Fin d → ℝ) (s : ℝ)
    (g : Fin d → ℝ) (x : X) :
    linearGaussian (affineGaussianCoefficients C A s) g x =
      linearGaussian C g x + s * linearGaussian A g x := by
  simp only [linearGaussian, affineGaussianCoefficients, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

def affineGaussianMean {d : ℕ} (w H : X → ℝ) (C A : X → Fin d → ℝ) (s : ℝ) : ℝ :=
  ∫ g, Real.log (finitePartition w (fun x => H x +
    linearGaussian (affineGaussianCoefficients C A s) g x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def affineGaussianSlope {d : ℕ} (w H : X → ℝ) (C A : X → Fin d → ℝ) (s : ℝ) : ℝ :=
  ∫ g, ∑ x, gaussianGibbs w H (affineGaussianCoefficients C A s) g x * linearGaussian A g x
    ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

lemma affineGaussianMean_hasDerivAt {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (affineGaussianMean w H C A) (affineGaussianSlope w H C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g => Real.log (finitePartition w
      (fun x => H x + linearGaussian (affineGaussianCoefficients C A s) g x))) μ := by
    simpa only [one_mul] using
      (continuous_log_finitePartition hw H (affineGaussianCoefficients C A s) 1).aestronglyMeasurable
  have hi : Integrable (fun g => Real.log (finitePartition w
      (fun x => H x + linearGaussian (affineGaussianCoefficients C A t) g x))) μ := by
    simpa only [one_mul] using integrable_log_finitePartition hw H (affineGaussianCoefficients C A t) 1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x, gaussianGibbs w H (affineGaussianCoefficients C A s) g x *
      linearGaussian A g x) (bound := fun g => ∑ x, |linearGaussian A g x|)
    (Filter.univ_mem) (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · exact (continuous_finsetSum _ (fun x _ =>
      (continuous_gaussianGibbs hw H _ x).mul (by unfold linearGaussian; fun_prop))).aestronglyMeasurable
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    exact finiteGibbs_average_bound hw _ _ (fun x =>
      Finset.single_le_sum (fun y _ => abs_nonneg (linearGaussian A g y)) (Finset.mem_univ x))
  · exact integrable_finsetSum _ (fun x _ => (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    apply hasDerivAt_log_finitePartition hw
    intro x
    simp_rw [linearGaussian_affine]
    simpa only [one_mul, id_eq] using (((hasDerivAt_id s).mul_const (linearGaussian A g x)).const_add
      (linearGaussian C g x)).const_add (H x)

lemma expectedGaussianEnergy_abs_le {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (A C : X → Fin (d + 1) → ℝ) {K : ℝ}
    (hK : ∀ x y, |gaussianCross A C x y| ≤ K) :
    |∫ g, ∑ x, gaussianGibbs w H C g x * linearGaussian A g x
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)| ≤ 2 * K := by
  have hb (g : Fin (d + 1) → ℝ) (x : X) :
      |gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y| ≤ 2 * K := by
    have hh := finiteGibbs_average_bound hw (fun y => H y + linearGaussian C g y)
      (fun y => gaussianCross A C x y) (hK x)
    exact (abs_sub _ _).trans (by dsimp only [gaussianGibbs] at *; linarith [hK x x])
  have hc (x : X) : Integrable (fun g => gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y))
      (Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) := by
    apply Integrable.of_bound
      ((continuous_gaussianGibbs hw H C x).mul
        (continuous_const.sub (continuous_finsetSum _ (fun y _ =>
          (continuous_gaussianGibbs hw H C y).mul continuous_const)))).aestronglyMeasurable (2 * K)
    apply ae_of_all
    intro g
    change ‖gaussianGibbs w H C g x *
      (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show 0 ≤ gaussianGibbs w H C g x from finiteGibbs_nonneg hw _ x)]
    exact (mul_le_mul_of_nonneg_right (finiteGibbs_le_one hw _ x) (abs_nonneg _)).trans
      (by simpa only [one_mul] using hb g x)
  rw [integral_finsetSum _ (fun x _ => by
    simpa only [mul_comm] using integrable_linearGaussian_mul_gibbs hw H A C x x)]
  simp_rw [mul_comm (gaussianGibbs w H C _ _) (linearGaussian A _ _),
    gaussian_gibbs_insertion hw H A C]
  rw [← integral_finsetSum _ (fun x _ => hc x)]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1))
      (f := fun g => ∑ x, gaussianGibbs w H C g x *
        (gaussianCross A C x x - ∑ y, gaussianGibbs w H C g y * gaussianCross A C x y))
      (C := 2 * K) (ae_of_all _ (fun g => by
        rw [Real.norm_eq_abs]
        exact finiteGibbs_average_bound hw (fun x => H x + linearGaussian C g x) _ (hb g))))

/-- A dimension-independent mean comparison. The cross-covariance of the
increment with the interpolated field, rather than the Gaussian coordinate
count, determines the bound. -/
theorem affineGaussianMean_abs_sub_le {d : ℕ} {w : X → ℝ} (hw : GibbsReference w)
    (H : X → ℝ) (C A : X → Fin (d + 1) → ℝ) {K : ℝ}
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x y,
      |gaussianCross A (affineGaussianCoefficients C A s) x y| ≤ K) :
    |affineGaussianMean w H C A 1 - affineGaussianMean w H C A 0| ≤ 2 * K := by
  have hd (s : ℝ) := affineGaussianMean_hasDerivAt hw H C A s
  have hb (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : |affineGaussianSlope w H C A s| ≤ 2 * K :=
    expectedGaussianEnergy_abs_le hw H A (affineGaussianCoefficients C A s) (hK s hs)
  simpa only [Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01'
      (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => by simpa only [Real.norm_eq_abs] using hb s (Set.Ico_subset_Icc_self hs))

end InvariantIsing

end

end OAI
