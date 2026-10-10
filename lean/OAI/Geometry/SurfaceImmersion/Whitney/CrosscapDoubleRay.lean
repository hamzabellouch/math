import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticCrosscapIsolation

namespace OAI

/-! The image of the local double curve is an actual regular half-ray.
Its acceleration is forced to be nonzero by the regular direction jet. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma crosscap_kernel_acceleration_ne_zero {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (b : Bool) (z : Base × ℝ)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) z)) :
    fderiv ℝ (fderiv ℝ f) z.1 (tangentRay b z.2) (tangentRay b z.2) ≠ 0 := by
  intro hz
  rw [(surfaceDirection_hasFDerivAt hf b z).fderiv] at hreg
  have he : surfaceDirectionLinearization f b z (tangentRay b z.2,0) =
      surfaceDirectionLinearization f b z 0 := by
    change fderiv ℝ f z.1 ((0:ℝ) • tangentRayVelocity b)+
      fderiv ℝ (fderiv ℝ f) z.1 (tangentRay b z.2) (tangentRay b z.2) = _
    simp only [hz,zero_smul,map_zero,add_zero]
  have hzero := congrArg Prod.fst (hreg he)
  exact tangentRay_ne_zero b z.2 hzero

lemma centeredSurfaceTaylor_value {f : Base → ProjectionTarget 3}
    (a v : Base) :
    centeredSurfaceTaylor f a (a+v) =
      f a+fderiv ℝ f a v+(1/2 : ℝ) • fderiv ℝ (fderiv ℝ f) a v v := by
  have hfirst : fderiv ℝ (translatedSurface f a) = fun y => fderiv ℝ f (y+a) := by
    funext y
    exact fderiv_comp_add_right a
  unfold centeredSurfaceTaylor surfaceTaylorTwo surfaceQuadratic
  rw [hfirst,fderiv_comp_add_right]
  simp only [translatedSurface,zero_add,add_sub_cancel_left]

lemma crosscap_kernel_image {f : Base → ProjectionTarget 3}
    (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0) (s : ℝ) :
    centeredSurfaceTaylor f a (a+s • tangentRay b t) =
      f a+((s*s)/2) • fderiv ℝ (fderiv ℝ f) a (tangentRay b t) (tangentRay b t) := by
  rw [centeredSurfaceTaylor_value]
  have hker : fderiv ℝ f a (tangentRay b t) = 0 := hz
  simp only [map_smul,hker,smul_zero,add_zero,smul_apply,smul_smul]
  congr 1
  congr 1
  ring

lemma crosscap_double_ray_injective {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hreg : Function.Injective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    Function.Injective (fun u : ℝ =>
      f a+u • fderiv ℝ (fderiv ℝ f) a (tangentRay b t) (tangentRay b t)) := by
  intro u v he
  have hn := crosscap_kernel_acceleration_ne_zero hf b (a,t) hreg
  have hs : (u-v) • fderiv ℝ (fderiv ℝ f) a (tangentRay b t) (tangentRay b t) = 0 := by
    rw [sub_smul,sub_eq_zero]
    exact add_left_cancel he
  exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right hn)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
