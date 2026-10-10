import OAI.Geometry.SurfaceImmersion.Correction.PolynomialRotationFrame
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs

namespace OAI

/-! An explicit relative filling of the twice-winding planar frame.
The third quaternion coordinate is a compact bump; no square-root choice
or topological extension assumption is needed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def doubleRotationFrame (x : Base) : Base →L[ℝ] FrameTarget :=
  polynomialRotationFrame (x 0) (x 1) 0

def filledDoubleRotation (χ : Base → ℝ) (x : Base) : Base →L[ℝ] FrameTarget :=
  polynomialRotationFrame (x 0) (x 1) (χ x)

lemma filledDoubleRotation_smooth {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (filledDoubleRotation χ) := by
  have hu : ContDiff ℝ ∞ (fun x : Base => rotationFirst (x 0) (x 1) (χ x)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationFirst] <;> fun_prop
  have hv : ContDiff ℝ ∞ (fun x : Base => rotationSecond (x 0) (x 1) (χ x)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [rotationSecond] <;> fun_prop
  exact (contDiff_const.smulRight hu).add (contDiff_const.smulRight hv)

lemma filledDoubleRotation_injective {χ : Base → ℝ} (hχ : χ 0 ≠ 0) (x : Base) :
    Function.Injective (filledDoubleRotation χ x) := by
  apply polynomialRotationFrame_injective
  by_cases hx : x = 0
  · subst x
    simpa using sq_pos_of_ne_zero hχ
  · have hn : (x 0)^2+(x 1)^2 > 0 := by
      by_cases h0 : x 0 = 0
      · have h1 : x 1 ≠ 0 := by
          intro h1
          apply hx
          ext i
          fin_cases i
          · exact h0
          · exact h1
        simpa [h0] using sq_pos_of_ne_zero h1
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (sq_nonneg _)
    exact add_pos_of_pos_of_nonneg hn (sq_nonneg _)

lemma filledDoubleRotation_exterior {χ : Base → ℝ} {x : Base}
    (hx : x ∉ tsupport χ) :
    filledDoubleRotation χ =ᶠ[𝓝 x] doubleRotationFrame := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  change χ y = 0 at hy
  simp only [filledDoubleRotation,doubleRotationFrame,hy]

/-- The first column is allowed to move in the interior. On the exterior
both columns are exactly those of the squared planar direction. -/
theorem compact_double_rotation_filling {U : Set Base} (hU : IsOpen U) (h0 : 0 ∈ U) :
    ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧ IsCompact K ∧ K ⊆ U ∧
      ∀ x ∉ K, A =ᶠ[𝓝 x] doubleRotationFrame := by
  obtain ⟨χ,hχ,hχc,_hχrange,hχsupp,hχone⟩ :=
    CollarVelocity.compact_cutoff (isCompact_singleton (x := (0 : Base))) hU
      (singleton_subset_iff.mpr h0)
  refine ⟨filledDoubleRotation χ,tsupport χ,filledDoubleRotation_smooth hχ,
    filledDoubleRotation_injective ?_,hχc,hχsupp,fun x hx => filledDoubleRotation_exterior hx⟩
  rw [hχone 0 (mem_singleton 0)]
  norm_num

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
