import OAI.Geometry.SurfaceImmersion.Whitney.QuadraticDoublePoints
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapKernelLine

namespace OAI

/-! The prepared quadratic model has a single singularity in a fixed
neighborhood. Its two local sheets meet exactly along the kernel line. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem centeredSurfaceTaylor_isolated_crosscap {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r,
      (¬ Function.Injective (fderiv ℝ (centeredSurfaceTaylor f a) x) ↔ x = a) := by
  obtain ⟨r,g,hr,_hr1,_hg,he,_hout,_hsupp,hiso⟩ :=
    centered_quadratic_crosscap_preparation hf b a t hz hreg zero_lt_one
  obtain ⟨s,hs,hsg⟩ := Metric.eventually_nhds_iff.mp he.eventuallyEq_nhds
  refine ⟨min r s,lt_min hr hs,?_⟩
  intro x hx
  have hxr : x ∈ ball a r := ball_subset_ball (min_le_left _ _) hx
  have hxs : dist x a < s := (mem_ball.mp hx).trans_le (min_le_right _ _)
  rw [← (hsg hxs).fderiv_eq]
  exact hiso x hxr

lemma centeredSurfaceTaylor_reflected_difference {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a v : Base) :
    centeredSurfaceTaylor f a (a+v)-centeredSurfaceTaylor f a (a-v) =
      (2 : ℝ) • fderiv ℝ f a v := by
  have h := centeredSurfaceTaylor_midpoint_identity hf a (a+v) (a-v)
  have hm : (1/2 : ℝ) • ((a+v)+(a-v)) = a := by module
  have hd : (a+v)-(a-v) = (2 : ℝ) • v := by module
  rw [hm,hd,centeredSurfaceTaylor_fderiv hf] at h
  simpa only [sub_self,map_zero,add_zero,map_smul] using h.symm

lemma centeredSurfaceTaylor_reflected_eq_iff {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a v : Base) :
    centeredSurfaceTaylor f a (a+v) = centeredSurfaceTaylor f a (a-v) ↔
      fderiv ℝ f a v = 0 := by
  rw [← sub_eq_zero,centeredSurfaceTaylor_reflected_difference hf]
  exact smul_eq_zero.trans (or_iff_right (by norm_num : (2 : ℝ) ≠ 0))

theorem quadratic_crosscap_double_points {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (a : Base) (b : Bool) (t : ℝ)
    (hz : surfaceDirection f b (a,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection f b) (a,t))) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ ball a r, ∀ y ∈ ball a r, x ≠ y →
      (centeredSurfaceTaylor f a x = centeredSurfaceTaylor f a y ↔
        ∃ s : ℝ, s ≠ 0 ∧ x = a+s • tangentRay b t ∧ y = a-s • tangentRay b t) := by
  obtain ⟨r,hr,hiso⟩ := centeredSurfaceTaylor_isolated_crosscap hf a b t hz hreg
  refine ⟨r,hr,?_⟩
  intro x hx y hy hne
  constructor
  · intro hxy
    have hreflect := centeredSurfaceTaylor_double_reflection hf a
      (fun z hz h => (hiso z hz).mp h) hx hy hne hxy
    have hy' : y = a-(x-a) := by rw [hreflect]; module
    have hx' : x = a+(x-a) := by abel
    have hker : fderiv ℝ f a (x-a) = 0 := by
      apply (centeredSurfaceTaylor_reflected_eq_iff hf a (x-a)).mp
      simpa only [← hx',← hy'] using hxy
    have hline := (crosscap_kernel_line hf b (a,t) hz hreg.1 (x-a)).mp hker
    let s := tangentRayCoefficient b (x-a)
    have hxline : x = a+s • tangentRay b t := by
      change x = a+tangentRayCoefficient b (x-a) • tangentRay b t
      rw [← hline]
      abel
    have hyline : y = a-s • tangentRay b t := by rw [hy',hline]
    refine ⟨s,?_,hxline,hyline⟩
    intro hs
    apply hne
    rw [hxline,hyline,hs,zero_smul,add_zero,sub_zero]
  · rintro ⟨s,_hs,rfl,rfl⟩
    apply (centeredSurfaceTaylor_reflected_eq_iff hf a _).mpr
    rw [map_smul]
    change s • surfaceDirection f b (a,t) = 0
    rw [hz,smul_zero]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
