import OAI.Geometry.SurfaceImmersion.Geometry.C1ImmersionJets

namespace OAI

/-! Two affine charts for the tangent directions of a surface, and the
kernel criterion for a linear projection along a graph direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def tangentRay (b : Bool) (t : ℝ) : Base :=
  if b then ![t,1] else ![1,t]

lemma tangentRay_ne_zero (b : Bool) (t : ℝ) : tangentRay b t ≠ 0 := by
  cases b <;> intro h
  · have hh := congrFun h 0
    norm_num [tangentRay] at hh
  · have hh := congrFun h 1
    norm_num [tangentRay] at hh

lemma tangentRay_smooth (b : Bool) : ContDiff ℝ ∞ (tangentRay b) := by
  cases b <;> apply contDiff_pi.mpr <;> intro i <;> fin_cases i <;>
    first | exact contDiff_id | exact contDiff_const

lemma exists_tangentRay {v : Base} (hv : v ≠ 0) :
    ∃ (b : Bool) (t c : ℝ), c ≠ 0 ∧ v = c • tangentRay b t := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1]
    refine ⟨true,v 0 / v 1,v 1,h1,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 1 * (v 0 / v 1)
      field_simp
    · change v 1 = v 1 * 1
      rw [mul_one]
  · refine ⟨false,v 1 / v 0,v 0,h0,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 0 * 1
      rw [mul_one]
    · change v 1 = v 0 * (v 1 / v 0)
      field_simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def graphProjection (a : V) : V × ℝ →L[ℝ] V :=
  ContinuousLinearMap.fst ℝ V ℝ -
    (ContinuousLinearMap.snd ℝ V ℝ).smulRight a

@[simp] lemma graphProjection_apply (a : V) (x : V × ℝ) :
    graphProjection a x = x.1 - x.2 • a := rfl

lemma graphProjection_comp_injective (a : V) (H : Base →L[ℝ] V × ℝ)
    (hH : Function.Injective H)
    (ha : ∀ b t, (H (tangentRay b t)).2 ≠ 0 →
      a ≠ ((H (tangentRay b t)).2)⁻¹ • (H (tangentRay b t)).1) :
    Function.Injective ((graphProjection a).comp H) := by
  have hker (v : Base) (hv : graphProjection a (H v) = 0) : v = 0 := by
    by_contra hn
    obtain ⟨b,t,c,hc,he⟩ := exists_tangentRay hn
    have hz : graphProjection a (H (tangentRay b t)) = 0 := by
      rw [he,map_smul,map_smul] at hv
      exact (smul_eq_zero.mp hv).resolve_left hc
    have hfst : (H (tangentRay b t)).1 = (H (tangentRay b t)).2 • a :=
      sub_eq_zero.mp hz
    have hlast : (H (tangentRay b t)).2 ≠ 0 := by
      intro hlast
      have hh : H (tangentRay b t) = H 0 := by
        rw [map_zero]
        apply Prod.ext
        · change (H (tangentRay b t)).1 = 0
          simpa only [hlast,zero_smul] using hfst
        · exact hlast
      exact tangentRay_ne_zero b t (hH hh)
    apply ha b t hlast
    rw [hfst,smul_smul,inv_mul_cancel₀ hlast,one_smul]
  intro v w h
  apply sub_eq_zero.mp
  apply hker
  change graphProjection a (H v) = graphProjection a (H w) at h
  rw [map_sub,map_sub,h,sub_self]

lemma weightedJet_smooth {w : Base → ℝ} {l : Base → V}
    (hw : ContDiff ℝ ∞ w) (hl : ContDiff ℝ ∞ l) :
    ContDiff ℝ ∞ (weightedJet w l) := by
  exact (hw.smul (hl.fderiv_right (m := ∞) (by simp))).sub
    ((hw.fderiv_right (m := ∞) (by simp)).smulRight hl)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
