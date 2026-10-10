import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSobolevContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneStrongDerivative

namespace OAI

/-! Strong L2 time differentiability of the whole-plane scalar solution.
The derivative is the actual advection-diffusion right-hand side. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory Set
open scoped ContDiff

def planeTimeDerivative (ν : ℝ) (a : ℝ → Plane → Plane)
    (h w : ℝ → Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  scalarGenerator ν (a t) (w t) x + h t x

theorem PlaneScalarSolution.cylinder_generator {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) :
    ContDiffOn ℝ ∞ (Function.uncurry (planeTimeDerivative ν a h w))
      (Icc 0 T ×ˢ univ) := by
  have hl : ContDiffOn ℝ ∞ (fun p : ℝ × Plane => scalarLaplacian (w p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
    ContDiffOn.sum (fun j _ => hw.cylinder_second_spatialD hT j j)
  have hp : ContDiffOn ℝ ∞
      (fun p : ℝ × Plane => ∑ j : Fin 2, a p.1 p.2 j * spatialD j (w p.1) p.2)
      (Icc 0 T ×ˢ univ) :=
    ContDiffOn.sum (fun j _ => ((contDiff_apply ℝ ℝ j).comp ha).contDiffOn.mul
      (hw.cylinder_spatialD hT j))
  have hv : ContDiffOn ℝ ∞ (fun _ : ℝ × Plane => ν) (Icc 0 T ×ˢ univ) := contDiffOn_const
  have hc := ((hv.mul hl).sub hp).add hh.contDiffOn
  apply hc.congr
  rintro ⟨t, x⟩ _
  change ν * scalarLaplacian (w t) x - fderiv ℝ (w t) x (a t x) + h t x =
    ν * scalarLaplacian (w t) x -
    (∑ j : Fin 2, a t x j * spatialD j (w t) x) + h t x
  rw [scalar_directional_basis]

theorem scalarLaplacian_smooth {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (scalarLaplacian f) :=
  ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hf))

theorem PlaneScalarSolution.timeDerivative_slice_continuous {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h))
    {t : ℝ} (ht : t ∈ Icc 0 T) : Continuous (planeTimeDerivative ν a h w t) := by
  have hws := hw.slice_smooth ht
  have has : ContDiff ℝ ∞ (a t) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hhs : ContDiff ℝ ∞ (h t) := hh.comp (contDiff_const.prodMk contDiff_id)
  change Continuous (fun x => ν * scalarLaplacian (w t) x -
    fderiv ℝ (w t) x (a t x) + h t x)
  exact ((continuous_const.mul (scalarLaplacian_smooth hws).continuous).sub
    ((hws.fderiv_right (by simp)).clm_apply has).continuous).add hhs.continuous

private theorem continuousOn_time_slice {F : ℝ × Plane → ℝ} {S : Set ℝ}
    (hF : ContinuousOn F (S ×ˢ univ)) (x : Plane) :
    ContinuousOn (fun t => F (t, x)) S := by
  have hm : ContinuousOn (fun t : ℝ => (t, x)) S :=
    continuousOn_id.prodMk continuousOn_const
  exact ContinuousOn.comp hF hm (fun t ht => ⟨ht, mem_univ x⟩)

theorem PlaneScalarSolution.timeDerivative_time_continuous {T ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (x : Plane) :
    ContinuousOn (fun t => planeTimeDerivative ν a h w t x) (Icc 0 T) :=
  continuousOn_time_slice (hw.cylinder_generator hT ha hh).continuousOn x

theorem scalarGenerator_tail_bound {ν A B C : ℝ} (hν : 0 ≤ ν)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) {a : Plane → Plane} {h f : Plane → ℝ}
    (ha : ∀ x, ‖a x‖ ≤ A)
    (hfirst : ∀ x j, |spatialD j f x| ≤ B * derivativeTail x)
    (hsecond : ∀ x j k, |spatialD j (spatialD k f) x| ≤ B * derivativeTail x)
    (hh : ∀ x, |h x| ≤ C * derivativeTail x) (x : Plane) :
    |scalarGenerator ν a f x + h x| ≤ (2 * ν * B + 2 * A * B + C) * derivativeTail x := by
  have hl : |scalarLaplacian f x| ≤ 2 * B * derivativeTail x := by
    unfold scalarLaplacian
    calc
      _ ≤ ∑ j : Fin 2, |spatialD j (spatialD j f) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 2, B * derivativeTail x := Finset.sum_le_sum (fun j _ => hsecond x j j)
      _ = _ := by simp; ring
  have hv (j : Fin 2) : |a x j| ≤ A :=
    (show |a x j| ≤ ‖a x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (a x) j).trans (ha x)
  have hp : |fderiv ℝ f x (a x)| ≤ 2 * A * B * derivativeTail x := by
    rw [scalar_directional_basis]
    calc
      _ ≤ ∑ j : Fin 2, |a x j * spatialD j f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 2, A * (B * derivativeTail x) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hv j) (hfirst x j) (abs_nonneg _) hA
      _ = _ := by simp; ring
  have hn : |ν * scalarLaplacian f x| ≤ ν * (2 * B * derivativeTail x) := by
    rw [abs_mul, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left hl hν
  unfold scalarGenerator
  calc
    _ ≤ |ν * scalarLaplacian f x - fderiv ℝ f x (a x)| + |h x| := abs_add_le _ _
    _ ≤ |ν * scalarLaplacian f x| + |fderiv ℝ f x (a x)| + |h x| :=
      by linarith [abs_sub (ν * scalarLaplacian f x) (fderiv ℝ f x (a x))]
    _ ≤ ν * (2 * B * derivativeTail x) + 2 * A * B * derivativeTail x +
        C * derivativeTail x := by linarith [hh x]
    _ = _ := by ring

theorem PlaneScalarSolution.time_derivative_envelope (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 T, ∀ x,
      |planeTimeDerivative ν a h w t x| ≤ B * derivativeTail x := by
  obtain ⟨B, hB, hb⟩ := hw.uniform_jet2_tail hE hT hν ha hh hc hpos
  obtain ⟨A, hA, hab⟩ := hc.drift_bound ha T hT
  obtain ⟨C, hC, hcb⟩ := hc.source_tail_bound hh T hT
  refine ⟨2 * ν * B + 2 * A * B + C, by positivity, ?_⟩
  intro t ht x
  exact scalarGenerator_tail_bound hν.le hA hB (hab t ht)
    (fun y j => (hb t ht y).2.1 j) (fun y j k => (hb t ht y).2.2 j k)
    (fun y => by
      rw [abs_of_nonneg (hpos t ht y)]
      exact (hcb t ht y).trans
        (mul_le_mul_of_nonneg_left (planeTailProfile_le_derivativeTail y) hC)) x

theorem PlaneScalarSolution.strong_time_derivative (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    PlaneStrongDerivativeOn w (planeTimeDerivative ν a h w) (Icc 0 T) := by
  obtain ⟨B, _, hb⟩ := hw.time_derivative_envelope hE hT.le hν ha hh hc hpos
  have hi : Integrable (fun x => (B * derivativeTail x) ^ 2) := by
    convert derivativeTail_square_integrable.const_mul (B ^ 2) using 1
    funext x
    ring
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : Continuous (planeTimeDerivative ν a h w t) :=
    hw.timeDerivative_slice_continuous ha hh ht
  have hd : ∀ t ∈ Icc 0 T, ∀ x, HasDerivWithinAt (fun r => w r x)
      (planeTimeDerivative ν a h w t x) (Icc 0 T) t := hw.equation
  exact strongDerivativeOn_of_envelope (convex_Icc 0 T)
    (fun t ht => (hw.slice_smooth ht).continuous) hs hd hi hb

theorem PlaneScalarSolution.time_derivative_square_continuity (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    SquareDistanceContinuousOn (planeTimeDerivative ν a h w) (Icc 0 T) := by
  obtain ⟨B, _, hb⟩ := hw.time_derivative_envelope hE hT.le hν ha hh hc hpos
  have hi : Integrable (fun x => (B * derivativeTail x) ^ 2) := by
    convert derivativeTail_square_integrable.const_mul (B ^ 2) using 1
    funext x
    ring
  have hs (t : ℝ) (ht : t ∈ Icc 0 T) : Continuous (planeTimeDerivative ν a h w t) :=
    hw.timeDerivative_slice_continuous ha hh ht
  exact squareDistanceContinuousOn_of_envelope hs
    (hw.timeDerivative_time_continuous hT ha hh) hi hb

theorem PlaneScalarSolution.strong_time_regularity (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    PlaneStrongDerivativeOn w (planeTimeDerivative ν a h w) (Icc 0 T) ∧
      SquareDistanceContinuousOn (planeTimeDerivative ν a h w) (Icc 0 T) :=
  ⟨hw.strong_time_derivative hE hT hν ha hh hc hpos,
    hw.time_derivative_square_continuity hE hT hν ha hh hc hpos⟩

end ForcedComputation.VelocityDetector

end

end OAI
