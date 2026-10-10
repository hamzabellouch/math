import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRotationCurve

namespace OAI

/-! Differentiating the finite Gaussian interpolation while removing the
nonuniform cavity penalty. The derivative is nonnegative under the
pointwise covariance-error bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

variable {X : Type*} [Fintype X]

def cavityGaussianCurveMean {d : ℕ} (w H V : X → ℝ) (c : ℝ)
    (C A : X → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, Real.log (finitePartition w (fun x => cavityPenaltyCurve H V c t x +
    linearGaussian (cavityGaussianCurve C A t) g x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

def cavityGaussianCurveSlope {d : ℕ} (w H V : X → ℝ) (c : ℝ)
    (C A : X → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ g, ∑ x, gaussianGibbs w (cavityPenaltyCurve H V c t) (cavityGaussianCurve C A t) g x *
    (4 * c * Real.sin t * Real.cos t * V x + linearGaussian (cavityGaussianCurveDerivative C A t) g x)
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)

omit [Fintype X] in
lemma cavityPenaltyCurve_derivative_bound (V : X → ℝ) (c t : ℝ) (x : X) :
    |4 * c * Real.sin t * Real.cos t * V x| ≤ 4 * |c| * |V x| := by
  have hsc : |Real.sin t| * |Real.cos t| ≤ 1 := by
    exact (mul_le_mul (Real.abs_sin_le_one t) (Real.abs_cos_le_one t)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  calc
    _ = (4 * |c| * |V x|) * (|Real.sin t| * |Real.cos t|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      ring
    _ ≤ (4 * |c| * |V x|) * 1 := mul_le_mul_of_nonneg_left hsc (by positivity)
    _ = _ := mul_one _

lemma cavityGaussianCurveMean_hasDerivAt {d : ℕ} {w : X → ℝ}
    (hw : GibbsReference w) (H V : X → ℝ) (c : ℝ) (C A : X → Fin d → ℝ) (t : ℝ) :
    HasDerivAt (cavityGaussianCurveMean w H V c C A)
      (cavityGaussianCurveSlope w H V c C A t) t := by
  let μ := Measure.pi (fun _ : Fin d => gaussianReal 0 1)
  let B := fun g : Fin d → ℝ => ∑ x,
    (4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
  have hm (s : ℝ) : AEStronglyMeasurable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c s x + linearGaussian (cavityGaussianCurve C A s) g x))) μ := by
    simpa only [one_mul] using
      (continuous_log_finitePartition hw (cavityPenaltyCurve H V c s)
        (cavityGaussianCurve C A s) 1).aestronglyMeasurable
  have hi : Integrable (fun g => Real.log (finitePartition w
      (fun x => cavityPenaltyCurve H V c t x + linearGaussian (cavityGaussianCurve C A t) g x))) μ := by
    simpa only [one_mul] using
      integrable_log_finitePartition hw (cavityPenaltyCurve H V c t) (cavityGaussianCurve C A t) 1
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (s := Set.univ)
    (F' := fun s g => ∑ x,
      gaussianGibbs w (cavityPenaltyCurve H V c s) (cavityGaussianCurve C A s) g x *
      (4 * c * Real.sin s * Real.cos s * V x + linearGaussian (cavityGaussianCurveDerivative C A s) g x))
    (bound := B) Filter.univ_mem (Filter.Eventually.of_forall hm) hi ?_ ?_ ?_ ?_).2
  · apply Continuous.aestronglyMeasurable
    apply continuous_finsetSum
    intro x _
    exact (continuous_gaussianGibbs hw _ _ x).mul
      (continuous_const.add (by unfold linearGaussian; fun_prop))
  · apply ae_of_all
    intro g s _
    rw [Real.norm_eq_abs]
    apply finiteGibbs_average_bound hw
    intro x
    calc
      _ ≤ |4 * c * Real.sin s * Real.cos s * V x| +
          |linearGaussian (cavityGaussianCurveDerivative C A s) g x| := abs_add_le _ _
      _ ≤ 4 * |c| * |V x| + (|linearGaussian C g x| + |linearGaussian A g x|) :=
        add_le_add (cavityPenaltyCurve_derivative_bound V c s x)
          (cavityGaussianCurveDerivative_bound C A s g x)
      _ ≤ B g := by
        simpa only [B, add_assoc] using Finset.single_le_sum
          (f := fun x => 4 * |c| * |V x| + |linearGaussian C g x| + |linearGaussian A g x|)
          (fun _ _ => by positivity) (Finset.mem_univ x)
  · exact integrable_finsetSum _ (fun x _ =>
      ((integrable_const _).add (integrable_linearGaussian C x).abs).add
        (integrable_linearGaussian A x).abs)
  · apply ae_of_all
    intro g s _
    apply hasDerivAt_log_finitePartition hw
    intro x
    exact (cavityPenaltyCurve_hasDerivAt H V c s x).add (cavityGaussianCurve_hasDerivAt C A s g x)

theorem cavity_finite_gaussian_penalty_comparison {d : ℕ} {w : X → ℝ}
    (hw : GibbsReference w) (H V : X → ℝ) (c : ℝ) (C A : X → Fin (d + 1) → ℝ)
    (hCA : ∀ x y, gaussianCross C A x y = 0)
    (hK : ∀ x y, |gaussianCross A A x y - gaussianCross C C x y| ≤ c * (V x + V y)) :
    (∫ g, Real.log (finitePartition w (fun x => H x - 2 * c * V x + linearGaussian C g x))
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1)) ≤
    ∫ g, Real.log (finitePartition w (fun x => H x + linearGaussian A g x))
      ∂Measure.pi (fun _ : Fin (d + 1) => gaussianReal 0 1) := by
  have hd (s : ℝ) := cavityGaussianCurveMean_hasDerivAt hw H V c C A s
  have hslope (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
      0 ≤ cavityGaussianCurveSlope w H V c C A s := by
    have hsc : 0 ≤ Real.sin s * Real.cos s := by
      apply mul_nonneg
      · exact Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, Real.pi_pos])
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
    have h := cavity_gaussian_penalty_nonneg hw (cavityPenaltyCurve H V c s) V
      (cavityGaussianCurveDerivative C A s) (cavityGaussianCurve C A s)
      (c * Real.sin s * Real.cos s) (cavityGaussianCurve_cross_bound C A V c s hCA hK hsc)
    convert h using 1
    unfold cavityGaussianCurveSlope
    congr 1
    funext g
    congr 1
    funext x
    ring
  have hm : MonotoneOn (cavityGaussianCurveMean w H V c C A)
      (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)).continuousOn
      (fun s _ => (hd s).hasDerivWithinAt)
    intro s hs
    exact hslope s (interior_subset hs)
  have hp : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hm ⟨le_rfl, hp⟩ ⟨hp, le_rfl⟩ hp
  simpa only [cavityGaussianCurveMean, cavityPenaltyCurve, linearGaussian, cavityGaussianCurve,
    Real.cos_zero, Real.sin_zero, one_pow, mul_one, one_mul, zero_mul, add_zero,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_pow (by decide : 2 ≠ 0),
    mul_zero, sub_zero, zero_add] using h

end InvariantIsing

end

end OAI
