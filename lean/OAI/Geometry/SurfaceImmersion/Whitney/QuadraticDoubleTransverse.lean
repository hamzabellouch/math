import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapDoubleRay

namespace OAI

/-! Away from its endpoint the double curve of a quadratic crosscap is
transverse: the difference map on the two source sheets is a submersion. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def quadraticDoubleDifference (f : Base → ProjectionTarget 3) (a : Base)
    (z : Base × Base) : ProjectionTarget 3 :=
  centeredSurfaceTaylor f a z.1-centeredSurfaceTaylor f a z.2

lemma quadraticDoubleDifference_smooth (f : Base → ProjectionTarget 3) (a : Base) :
    ContDiff ℝ ∞ (quadraticDoubleDifference f a) :=
  ((centeredSurfaceTaylor_smooth f a).comp contDiff_fst).sub
    ((centeredSurfaceTaylor_smooth f a).comp contDiff_snd)

lemma quadraticDoubleDifference_fderiv (f : Base → ProjectionTarget 3)
    (a : Base) (z : Base × Base) (v : Base × Base) :
    fderiv ℝ (quadraticDoubleDifference f a) z v =
      fderiv ℝ (centeredSurfaceTaylor f a) z.1 v.1-
        fderiv ℝ (centeredSurfaceTaylor f a) z.2 v.2 := by
  have hQ := (centeredSurfaceTaylor_smooth f a).differentiable (by simp)
  exact congrArg (fun L : (Base × Base) →L[ℝ] ProjectionTarget 3 => L v)
    (((hQ z.1).hasFDerivAt.comp z hasFDerivAt_fst).sub
      ((hQ z.2).hasFDerivAt.comp z hasFDerivAt_snd)).fderiv

lemma quadraticDoubleDifference_at_kernel {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a w : Base) (s : ℝ) (u v : Base) :
    fderiv ℝ (quadraticDoubleDifference f a) (a+s • w,a-s • w) (u,v) =
      fderiv ℝ f a (u-v)+fderiv ℝ (fderiv ℝ f) a w (s • (u+v)) := by
  rw [quadraticDoubleDifference_fderiv,centeredSurfaceTaylor_fderiv hf,
    centeredSurfaceTaylor_fderiv hf]
  simp only [add_sub_cancel_left,sub_sub_cancel_left,
    map_smul,map_neg,add_apply,smul_apply,neg_apply,map_sub,map_add]
  module

theorem quadratic_crosscap_double_transverse {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hreg : Function.Surjective (fderiv ℝ (surfaceDirection f b) (a,t)))
    {s : ℝ} (hs : s ≠ 0) :
    Function.Surjective (fderiv ℝ (quadraticDoubleDifference f a)
      (a+s • tangentRay b t,a-s • tangentRay b t)) := by
  intro y
  obtain ⟨z,hz⟩ := hreg y
  let A : Base := z.2 • tangentRayVelocity b
  let C : Base := s⁻¹ • z.1
  let u := (1/2 : ℝ) • (A+C)
  let v := (1/2 : ℝ) • (C-A)
  have hd : u-v = A := by dsimp [u,v]; module
  have ha : s • (u+v) = z.1 := by
    have huv : u+v = C := by dsimp [u,v]; module
    rw [huv]
    dsimp [C]
    rw [smul_smul,mul_inv_cancel₀ hs,one_smul]
  refine ⟨(u,v),?_⟩
  rw [quadraticDoubleDifference_at_kernel hf,hd,ha]
  rw [(surfaceDirection_hasFDerivAt hf b (a,t)).fderiv] at hz
  have hsym : fderiv ℝ (fderiv ℝ f) a (tangentRay b t) z.1 =
      fderiv ℝ (fderiv ℝ f) a z.1 (tangentRay b t) :=
    hf.contDiffAt.isSymmSndFDerivAt (by simp) _ _
  rw [hsym]
  exact hz

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
