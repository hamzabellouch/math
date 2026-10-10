import OAI.Geometry.SurfaceImmersion.Geometry.CenteredTaylorJets

namespace OAI

/-! Double points of a quadratic crosscap have a singular midpoint. In a
neighborhood with one singular point their two preimages are reflections
through that point. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma surfaceTaylorTwo_midpoint_identity {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (x y : Base) :
    fderiv ℝ (surfaceTaylorTwo f) ((1/2 : ℝ) • (x+y)) (x-y) =
      surfaceTaylorTwo f x-surfaceTaylorTwo f y := by
  have hB : ∀ v w, fderiv ℝ (fderiv ℝ f) 0 v w = fderiv ℝ (fderiv ℝ f) 0 w v :=
    fun v w => hf.contDiffAt.isSymmSndFDerivAt (by simp) v w
  rw [surfaceTaylorTwo_fderiv hf]
  simp only [surfaceTaylorTwo,surfaceQuadratic,add_apply,
    map_smul,map_add,map_sub,smul_apply]
  rw [hB y x]
  module

lemma centeredSurfaceTaylor_midpoint_identity {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x y : Base) :
    fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) (x-y) =
      centeredSurfaceTaylor f a x-centeredSurfaceTaylor f a y := by
  have ht : ContDiff ℝ ∞ (translatedSurface f a) := hf.comp (contDiff_id.add contDiff_const)
  change fderiv ℝ (fun z => surfaceTaylorTwo (translatedSurface f a) (z-a)) _ _ = _
  rw [fderiv_comp_sub]
  have hm : (1/2 : ℝ) • (x+y)-a = (1/2 : ℝ) • ((x-a)+(y-a)) := by module
  have hd : x-y = (x-a)-(y-a) := by abel
  rw [hm,hd,surfaceTaylorTwo_midpoint_identity ht]
  rfl

lemma centeredSurfaceTaylor_double_midpoint_singular {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a x y : Base) (hne : x ≠ y)
    (heq : centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y) :
    ¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y))) := by
  intro hinj
  have hz : fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) (x-y) =
      fderiv ℝ (centeredSurfaceTaylor f a) ((1/2 : ℝ) • (x+y)) 0 := by
    rw [centeredSurfaceTaylor_midpoint_identity hf,heq,sub_self,map_zero]
  exact hne (sub_eq_zero.mp (hinj hz))

theorem centeredSurfaceTaylor_double_reflection {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) {r : ℝ}
    (hsing : ∀ z ∈ ball a r,
      ¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) z) → z = a)
    {x y : Base} (hx : x ∈ ball a r) (hy : y ∈ ball a r) (hne : x ≠ y)
    (heq : centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y) :
    y = (2 : ℝ) • a-x := by
  have hm : (1/2 : ℝ) • (x+y) ∈ ball a r := by
    have h := (convex_ball a r) hx hy (by norm_num : 0 ≤ (1/2 : ℝ))
      (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ)+(1/2) = 1)
    simpa only [smul_add] using h
  have he := hsing _ hm (centeredSurfaceTaylor_double_midpoint_singular hf a x y hne heq)
  have hsum : x+y = (2 : ℝ) • a := by
    have hh := congrArg (fun v : Base => (2 : ℝ) • v) he
    simpa only [smul_smul,show (2 : ℝ)*(1/2) = 1 by norm_num,one_smul] using hh
  calc
    y = (x+y)-x := by abel
    _ = (2 : ℝ) • a-x := by rw [hsum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
