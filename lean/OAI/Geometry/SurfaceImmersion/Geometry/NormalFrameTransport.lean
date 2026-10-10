import OAI.Geometry.SurfaceImmersion.Whitney.RelativeFramePatching
import OAI.Geometry.SurfaceImmersion.Atlas.NormalDefectCoordinates
import OAI.Geometry.SurfaceImmersion.Whitney.NormalizedFramedAxis

namespace OAI

/-! Exact algebra transporting a filled normalized frame to the derivative
of the original surface map. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def longitudinalShear (c : ℝ) : Base →L[ℝ] Base :=
  ContinuousLinearMap.id ℝ Base+(ContinuousLinearMap.proj 1).smulRight (![c,0] : Base)

lemma longitudinalShear_injective (c : ℝ) : Function.Injective (longitudinalShear c) := by
  intro u v he
  have h1 : u 1 = v 1 := by simpa [longitudinalShear] using congrFun he 1
  have h0 : u 0+u 1*c = v 0+v 1*c := congrFun he 0
  rw [h1] at h0
  ext i
  fin_cases i
  · exact add_right_cancel h0
  · exact h1

lemma longitudinalShear_smooth : ContDiff ℝ ∞ longitudinalShear := by
  have h : ContDiff ℝ ∞ (fun c : ℝ => (![c,0] : Base)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact contDiff_const.add (contDiff_const.smulRight h)

lemma defectFrame_shear_apply (N : Base → Base) (x : Base) (c : ℝ) (v : Base) :
    defectFrame N x (longitudinalShear c v) = ![v 0+v 1*c,v 1*N x 0,v 1*N x 1] := by
  ext i
  fin_cases i <;> simp [defectFrame,axisNormalFrame,longitudinalShear,Matrix.vecHead,Matrix.vecTail]

def normalOutput (d : Base) : FrameTarget →L[ℝ] (Base × ℝ) :=
  (ContinuousLinearMap.proj 0).smulRight ((0:Base),1)+
    (ContinuousLinearMap.proj 1).smulRight (planeComplexFrame d (![1,0] : Base),0)+
    (ContinuousLinearMap.proj 2).smulRight (planeComplexFrame d (![0,1] : Base),0)

lemma normalOutput_apply (d : Base) (v : FrameTarget) :
    normalOutput d v = (planeComplexFrame d ![v 1,v 2],v 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [normalOutput,planeComplexFrame_apply] <;> ring
  · simp [normalOutput]

lemma normalOutput_injective {d : Base} (hd : d ≠ 0) : Function.Injective (normalOutput d) := by
  intro u v he
  rw [normalOutput_apply,normalOutput_apply] at he
  have h12 := (planeComplexFrame_invertible hd).injective (congrArg Prod.fst he)
  ext i
  fin_cases i
  · exact congrArg Prod.snd he
  · exact congrFun h12 0
  · exact congrFun h12 1

lemma normalOutput_smooth : ContDiff ℝ ∞ normalOutput := by
  exact (contDiff_const.add (contDiff_const.smulRight
    ((planeComplexFrame_smooth.clm_apply contDiff_const).prodMk contDiff_const))).add
    (contDiff_const.smulRight
      ((planeComplexFrame_smooth.clm_apply contDiff_const).prodMk contDiff_const))

lemma frameTarget_plane_columns (L : Base →L[ℝ] FrameTarget) :
    L = (ContinuousLinearMap.proj 0).smulRight (L (![1,0] : Base))+
      (ContinuousLinearMap.proj 1).smulRight (L (![0,1] : Base)) := by
  ext v : 1
  have hv : v = v 0 • (![1,0] : Base)+v 1 • (![0,1] : Base) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [hv]
  rw [map_add,map_smul,map_smul]
  rfl

def longitudinalCoefficient (φ : Base → ProjectionTarget 3) (a : FrameTarget) (x : Base) : ℝ :=
  ((curveNormalLinear (transverseDerivative φ x) a).inverse
    (coordinateDifferential φ x (![0,1] : Base))).2

def transportedNormalFrame (φ : Base → ProjectionTarget 3) (a : FrameTarget)
    (d : ℝ → Base) (B : Base → Base →L[ℝ] FrameTarget) (x : Base) :
    Base →L[ℝ] FrameTarget :=
  (curveNormalLinear (transverseDerivative φ x) a).comp
    ((normalOutput (d (x 1))).comp ((B x).comp (longitudinalShear (longitudinalCoefficient φ a x))))

lemma transportedNormalFrame_injective {φ : Base → ProjectionTarget 3} {a : FrameTarget}
    {d : ℝ → Base} {B : Base → Base →L[ℝ] FrameTarget} {x : Base}
    (hu : transverseDerivative φ x ≠ 0) (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a)
    (hd : d (x 1) ≠ 0) (hB : Function.Injective (B x)) :
    Function.Injective (transportedNormalFrame φ a d B x) :=
  (curveNormalLinear_bijective hu ha).1.comp ((normalOutput_injective hd).comp
    (hB.comp (longitudinalShear_injective _)))

lemma transportedNormalFrame_exact (φ : Base → ProjectionTarget 3) (a : FrameTarget)
    (d : ℝ → Base) (x : Base) (hu : transverseDerivative φ x ≠ 0)
    (ha : ∀ r : ℝ, r • transverseDerivative φ x ≠ a) (hd : d (x 1) ≠ 0) :
    transportedNormalFrame φ a d (defectFrame (axisNormalizedDefect d (normalDefect φ a))) x =
      coordinateDifferential φ x := by
  let T := curveNormalLinear (transverseDerivative φ x) a
  have hT := curveNormalLinear_invertible hu ha
  have hP := planeComplexFrame_invertible hd
  have hL := frameTarget_plane_columns (coordinateDifferential φ x)
  rw [hL]
  ext v : 1
  change T (normalOutput (d (x 1))
    (defectFrame (axisNormalizedDefect d (normalDefect φ a)) x (longitudinalShear (longitudinalCoefficient φ a x) v))) = _
  rw [defectFrame_shear_apply,normalOutput_apply]
  have he : planeComplexFrame (d (x 1)) (axisNormalizedDefect d (normalDefect φ a) x) = normalDefect φ a x :=
    hP.self_apply_inverse _
  have hz : (![v 1 * axisNormalizedDefect d (normalDefect φ a) x 0,
      v 1 * axisNormalizedDefect d (normalDefect φ a) x 1] : Base) =
      v 1 • axisNormalizedDefect d (normalDefect φ a) x := by ext i; fin_cases i <;> rfl
  change T (planeComplexFrame (d (x 1))
    ![v 1 * axisNormalizedDefect d (normalDefect φ a) x 0,
      v 1 * axisNormalizedDefect d (normalDefect φ a) x 1],
    v 0+v 1*longitudinalCoefficient φ a x) = _
  rw [hz,map_smul,he]
  have hepair : (v 1 • normalDefect φ a x,v 0+v 1*longitudinalCoefficient φ a x) =
      v 0 • ((0:Base),1)+v 1 • T.inverse (coordinateDifferential φ x ![0,1]) := by
    apply Prod.ext
    · simp [normalDefect,T]
    · simp [longitudinalCoefficient,T]
  rw [hepair,map_add,map_smul,map_smul,hT.self_apply_inverse]
  have hvel : T ((0:Base),1) = coordinateDifferential φ x ![1,0] := by
    simp [T,curveNormalLinear_apply,transverseDerivative]
  rw [hvel]
  rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
