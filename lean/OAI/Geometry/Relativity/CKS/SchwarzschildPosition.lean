import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.SchwarzschildCoordinates

namespace OAI

noncomputable section
open Set Filter Manifold Bundle Function
open scoped ContDiff Topology InnerProductSpace
namespace CKSSchwarzschild
open CKSBoundarySurface
local instance : Fact (Module.finrank ℝ E3 = 2+1) := ⟨by simp⟩

lemma radius_pos {m : ℝ} (hm : 0 < m) (p : Exterior) : 0 < radius m p := by
  have hp := p.1.property
  unfold radius height
  linarith
lemma radius_ge (m : ℝ) (p : Exterior) : 2*m ≤ radius m p := by
  have hp := p.1.property
  unfold radius height
  linarith
lemma radius_smooth (m : ℝ) : ContMDiff I3 𝓘(ℝ,ℝ) ∞ (radius m) :=
  contMDiff_const.add height_smooth
lemma directionAmbient_smooth : ContMDiff I3 𝓘(ℝ,E3) ∞ directionAmbient :=
  (contMDiff_coe_sphere (n := 2) (E := E3)).comp angular_smooth
lemma position_smooth (m : ℝ) : ContMDiff I3 𝓘(ℝ,E3) ∞ (position m) :=
  (radius_smooth m).smul directionAmbient_smooth
lemma norm_direction (p : Exterior) : ‖directionAmbient p‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right,directionAmbient] using p.2.property
lemma norm_position {m : ℝ} (hm : 0 < m) (p : Exterior) : ‖position m p‖ = radius m p := by
  rw [position,norm_smul,norm_direction,mul_one,Real.norm_eq_abs,abs_of_pos (radius_pos hm p)]
lemma position_ne_zero {m : ℝ} (hm : 0 < m) (p : Exterior) : position m p ≠ 0 := by
  exact norm_ne_zero_iff.mp ((norm_position hm p).trans_ne (ne_of_gt (radius_pos hm p)))

lemma mfderiv_radius (m : ℝ) (p : Exterior) : mfderiv I3 𝓘(ℝ,ℝ) (radius m) p = firstCoordinate := by
  have h := (hasMFDerivAt_const (I := I3) (I' := 𝓘(ℝ,ℝ)) (2*m) p).add
    ((height_smooth p).mdifferentiableAt (by simp)).hasMFDerivAt
  have he := h.mfderiv
  rw [mfderiv_height] at he
  change mfderiv I3 𝓘(ℝ,ℝ) (radius m) p = (0 : E3 →L[ℝ] ℝ) + firstCoordinate at he
  simpa only [zero_add] using he

lemma mfderiv_directionAmbient (p : Exterior) :
    mfderiv I3 𝓘(ℝ,E3) directionAmbient p =
      (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2).comp dropPlane := by
  have h := mfderiv_comp (I := I3) (I' := I2) (I'' := 𝓘(ℝ,E3))
    (f := angular) (g := (Subtype.val : Sphere → E3)) p
    ((contMDiff_coe_sphere (n := 2) (m := ∞) p.2).mdifferentiableAt (by simp))
    ((angular_smooth p).mdifferentiableAt (by simp))
  rw [mfderiv_angular] at h
  exact h

lemma directionAmbient_orthogonal (p : Exterior) (v : E3) :
    ⟪directionAmbient p, mfderiv I3 𝓘(ℝ,E3) directionAmbient p v⟫_ℝ = 0 := by
  rw [mfderiv_directionAmbient]
  have h : (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2).range =
      (ℝ ∙ (p.2.val : E3))ᗮ := by
    convert! range_mvfderiv_subtypeVal (n := 2) p.2
  have hv : (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2) (dropPlane v) ∈
      (ℝ ∙ (p.2.val : E3))ᗮ := by
    rw [← h]
    exact ⟨dropPlane v,rfl⟩
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hv)

def ambientDerivative (f : Exterior → E3) (p : Exterior) : E3 →L[ℝ] E3 := by
  exact mfderiv I3 𝓘(ℝ,E3) f p

lemma mfderiv_position (m : ℝ) (p : Exterior) (v : E3) :
    ambientDerivative (position m) p v =
      (radius m p) • ambientDerivative directionAmbient p v +
        (v 0) • directionAmbient p := by
  have hr := ((radius_smooth m p).mdifferentiableAt (by simp)).hasMFDerivAt
  have hn := ((directionAmbient_smooth p).mdifferentiableAt (by simp)).hasMFDerivAt
  let D : E3 →L[ℝ] E3 :=
    (radius m p) • ambientDerivative directionAmbient p +
      firstCoordinate.smulRight (directionAmbient p)
  have hd : HasMFDerivAt I3 𝓘(ℝ,E3) (position m) p D := by
    refine ⟨(position_smooth m).continuous.continuousAt,?_⟩
    have h := hr.2.smul hn.2
    simp only [writtenInExtChartAt,Function.comp_apply,mfld_simps,
      mfderiv_radius,chartAt_self_eq] at h
    change HasFDerivWithinAt (writtenInExtChartAt I3 𝓘(ℝ,E3) p (position m)) D
      (range I3) (extChartAt I3 p p) at h
    exact h

  exact congrArg (fun L => L v) hd.mfderiv

lemma position_derivative_injective {m : ℝ} (hm : 0 < m) (p : Exterior) :
    Injective (ambientDerivative (position m) p) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hv' := hv
  change ambientDerivative (position m) p v = 0 at hv'
  rw [mfderiv_position] at hv'
  change radius m p • ambientDerivative directionAmbient p v + (v 0) • directionAmbient p = 0 at hv'
  have hinner := congrArg (fun w : E3 => ⟪directionAmbient p,w⟫_ℝ) hv'
  have hn : ⟪directionAmbient p,directionAmbient p⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq,norm_direction]; norm_num
  have ho : ⟪directionAmbient p,ambientDerivative directionAmbient p v⟫_ℝ = 0 :=
    directionAmbient_orthogonal p v
  simp only [inner_add_right,inner_smul_right,ho,hn,mul_zero,mul_one,
    zero_add,inner_zero_right] at hinner
  have hdir : mfderiv I3 𝓘(ℝ,E3) directionAmbient p v = 0 := by
    rw [hinner,zero_smul,add_zero] at hv'
    exact (smul_eq_zero.mp hv').resolve_left (ne_of_gt (radius_pos hm p))
  have hdrop : dropPlane v = 0 := by
    rw [mfderiv_directionAmbient] at hdir
    have injectiveSphere : Injective (mfderiv I2 𝓘(ℝ,E3) (Subtype.val : Sphere → E3) p.2) := by
      convert! injective_mvfderiv_subtypeVal_sphere (n := 2) p.2
    exact injectiveSphere (hdir.trans (map_zero _).symm)
  rw [← join_drop v,hinner,hdrop]
  exact map_zero _

end CKSSchwarzschild

end

end OAI
