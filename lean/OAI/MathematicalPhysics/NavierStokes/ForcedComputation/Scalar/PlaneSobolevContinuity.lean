import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSobolevSlices
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCylinderCalculus
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneSquareContinuity

namespace OAI

/-! The scalar and its first two spatial derivatives vary continuously in
L2 on each closed finite time interval. This is the spatial H2 time condition. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian MeasureTheory Set
open scoped ContDiff

theorem planeTailProfile_le_derivativeTail (x : Plane) :
    planeTailProfile x ≤ derivativeTail x := by
  have h0 := (derivativeTail_pos x).le
  have h1 := derivativeTail_le_one x
  have hs : derivativeTail x ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have hm := mul_le_mul_of_nonneg_left hs h0
  rw [← derivativeTail_cube]
  nlinarith

theorem PlaneScalarSolution.uniform_jet2_tail (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 ≤ T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc 0 T, ∀ x,
      |w t x| ≤ A * derivativeTail x ∧
      (∀ j, |spatialD j (w t) x| ≤ A * derivativeTail x) ∧
      (∀ j k, |spatialD j (spatialD k (w t)) x| ≤ A * derivativeTail x) := by
  obtain ⟨B, hB, htail⟩ := hw.uniform_tail_bound hT hν.le ha hh hc hpos
  obtain ⟨N, hN⟩ := hw.spatial_bounds hE hT hν ha hh hc
  let M := max 0 N
  have hM : 0 ≤ M := le_max_left _ _
  let A := B + 3 * (100 * B + M)
  have hBA : B ≤ A := by dsimp [A]; nlinarith
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro t ht x
  have h2 : ∀ y, ‖iteratedFDeriv ℝ 2 (w t) y‖ ≤ M :=
    fun y => (hN t ht 2 (by omega) y).trans (le_max_right _ _)
  have h3 : ∀ y, ‖iteratedFDeriv ℝ 3 (w t) y‖ ≤ M :=
    fun y => (hN t ht 3 le_rfl y).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · exact (htail t ht x).trans ((mul_le_mul_of_nonneg_left
      (planeTailProfile_le_derivativeTail x) hB).trans
        (mul_le_mul_of_nonneg_right hBA (derivativeTail_pos x).le))
  · intro j
    apply (scalar_gradient_entry_tail (hw.slice_smooth ht) hB hM (htail t ht) h2 x j).trans
    apply mul_le_mul_of_nonneg_right _ (derivativeTail_pos x).le
    dsimp [A]
    nlinarith
  · intro j k
    apply (scalar_hessian_entry_tail (hw.slice_smooth ht) hB hM (htail t ht) h3 x j k).trans
    apply mul_le_mul_of_nonneg_right _ (derivativeTail_pos x).le
    dsimp [A]
    linarith

def PlaneH2ContinuousOn (w : ℝ → Plane → ℝ) (S : Set ℝ) : Prop :=
  SquareDistanceContinuousOn w S ∧
    (∀ j, SquareDistanceContinuousOn (fun t => spatialD j (w t)) S) ∧
    (∀ j k, SquareDistanceContinuousOn (fun t => spatialD j (spatialD k (w t))) S)

theorem PlaneScalarSolution.h2_continuousOn (hE : PlaneScalarExistence)
    {T ν : ℝ} {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : PlaneScalarSolution T ν a h w) (hT : 0 < T) (hν : 0 < ν)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hh : ContDiff ℝ ∞ (Function.uncurry h)) (hc : CompactPlaneCoefficients a h)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ h t x) :
    PlaneH2ContinuousOn w (Icc 0 T) := by
  obtain ⟨A, _, hA⟩ := hw.uniform_jet2_tail hE hT.le hν ha hh hc hpos
  have hi : Integrable (fun x => (A * derivativeTail x) ^ 2) := by
    convert derivativeTail_square_integrable.const_mul (A ^ 2) using 1
    funext x
    ring
  have hcurry {F : ℝ × Plane → ℝ}
      (hF : ContinuousOn F (Icc 0 T ×ˢ univ)) (x : Plane) :
      ContinuousOn (fun t => F (t, x)) (Icc 0 T) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ x⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact squareDistanceContinuousOn_of_envelope (fun t ht => (hw.slice_smooth ht).continuous)
      (fun x => hcurry hw.smooth.continuousOn x) hi (fun t ht x => (hA t ht x).1)
  · intro j
    exact squareDistanceContinuousOn_of_envelope
      (fun t ht => (spatialD_smooth j (hw.slice_smooth ht)).continuous)
      (fun x => hcurry (hw.cylinder_spatialD hT j).continuousOn x)
      hi (fun t ht x => (hA t ht x).2.1 j)
  · intro j k
    exact squareDistanceContinuousOn_of_envelope
      (fun t ht => (spatialD_smooth j (spatialD_smooth k (hw.slice_smooth ht))).continuous)
      (fun x => hcurry (hw.cylinder_second_spatialD hT j k).continuousOn x)
      hi (fun t ht x => (hA t ht x).2.2 j k)

end ForcedComputation.VelocityDetector

end

end OAI
