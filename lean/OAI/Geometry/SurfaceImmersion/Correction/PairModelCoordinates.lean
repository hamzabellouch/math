import OAI.Geometry.SurfaceImmersion.Geometry.RelativeDefectFilling
import OAI.Geometry.SurfaceImmersion.Whitney.OppositeIndexFrameFilling

namespace OAI

/-! Affine coordinates and invertible normal rescalings for the model pair. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def pairCoordinateMap (c h k : ℝ) (x : Base) : Base := ![(x 1-c)/h,k*x 0]
def pairCoordinateInverse (c h k : ℝ) (y : Base) : Base := ![y 1/k,c+h*y 0]

lemma pairCoordinateMap_smooth (c h k : ℝ) : ContDiff ℝ ∞ (pairCoordinateMap c h k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pairCoordinateMap] <;> fun_prop
lemma pairCoordinateInverse_smooth (c h k : ℝ) : ContDiff ℝ ∞ (pairCoordinateInverse c h k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pairCoordinateInverse] <;> fun_prop

def pairCoordinates (c h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) : Base ≃ₜ Base where
  toFun := pairCoordinateMap c h k
  invFun := pairCoordinateInverse c h k
  left_inv := by
    intro x
    ext i
    fin_cases i
    · change (k*x 0)/k = x 0
      field_simp
    · change c+h*((x 1-c)/h) = x 1
      field_simp
      ring
  right_inv := by
    intro x
    ext i
    fin_cases i
    · change (c+h*x 0-c)/h = x 0
      field_simp
      ring
    · change k*(x 1/k) = x 1
      field_simp
  continuous_toFun := (pairCoordinateMap_smooth c h k).continuous
  continuous_invFun := (pairCoordinateInverse_smooth c h k).continuous

def normalPairScale (a b : ℝ) : FrameTarget →L[ℝ] FrameTarget :=
  (ContinuousLinearMap.proj 0).smulRight (![1,0,0] : FrameTarget)+
  (ContinuousLinearMap.proj 1).smulRight (![0,a,0] : FrameTarget)+
  (ContinuousLinearMap.proj 2).smulRight (![0,0,b] : FrameTarget)

lemma normalPairScale_apply (a b : ℝ) (v : FrameTarget) :
    normalPairScale a b v = ![v 0,a*v 1,b*v 2] := by
  ext i
  fin_cases i <;> simp [normalPairScale,mul_comm]

lemma normalPairScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (normalPairScale a b) := by
  intro u v he
  rw [normalPairScale_apply,normalPairScale_apply] at he
  ext i
  fin_cases i
  · exact congrFun he 0
  · exact mul_left_cancel₀ ha (congrFun he 1)
  · exact mul_left_cancel₀ hb (congrFun he 2)

lemma normalPairScale_axis (a b r y z : ℝ) :
    (normalPairScale a b).comp (axisNormalFrame r y z) = axisNormalFrame r (a*y) (b*z) := by
  ext v i
  fin_cases i <;> simp [normalPairScale,axisNormalFrame] <;> ring

/-- Pull a compact model filling back by an affine chart and rescale its two
normal coordinates. The support is the actual inverse image of the model support. -/
theorem pullback_model_filling {Q : Base → Base →L[ℝ] FrameTarget}
    {B : Base → Base →L[ℝ] FrameTarget} (hB : ContDiff ℝ ∞ B)
    (hBI : ∀ x, Function.Injective (B x)) {K : Set Base} (hK : IsCompact K)
    (hBe : ∀ x ∉ K, B =ᶠ[𝓝 x] Q)
    (c h k a b : ℝ) (hh : h ≠ 0) (hk : k ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ A : Base → Base →L[ℝ] FrameTarget,
      ContDiff ℝ ∞ A ∧ (∀ x, Function.Injective (A x)) ∧
      IsCompact ((pairCoordinates c h k hh hk) ⁻¹' K) ∧
      ∀ x ∉ (pairCoordinates c h k hh hk) ⁻¹' K,
        A x = (normalPairScale a b).comp (Q (pairCoordinateMap c h k x)) := by
  let e := pairCoordinates c h k hh hk
  let A := fun x => (normalPairScale a b).comp (B (e x))
  refine ⟨A,contDiff_const.clm_comp (hB.comp (pairCoordinateMap_smooth c h k)),?_,?_,?_⟩
  · intro x
    exact (normalPairScale_injective ha hb).comp (hBI (e x))
  · exact e.isCompact_preimage.mpr hK
  · intro x hx
    have he : B (e x) = Q (e x) := (hBe (e x) hx).eq_of_nhds
    dsimp [A]
    rw [he]
    rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
