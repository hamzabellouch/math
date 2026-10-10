import OAI.MeasureTheory.Falconer.Angular.GnomonicChart
import OAI.MeasureTheory.Falconer.Geometry.PlanarSlopeBalls

import OAI.MeasureTheory.Falconer.Angular.PublishedGnomonic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

namespace Falconer
open NormedSpace
variable {n : ℕ}

noncomputable def gnomonicCoordinates (w : Sphere (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => (w:Space (n+1)) i.succ / (w:Space (n+1)) 0)

@[simp] theorem gnomonicCoordinates_apply (w : Sphere (n+1)) (i : Fin n) :
    gnomonicCoordinates w i = (w:Space (n+1)) i.succ / (w:Space (n+1)) 0 := rfl

theorem gnomonicCoordinates_measurable : Measurable (@gnomonicCoordinates n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply Measurable.of_eval
  intro i
  fun_prop

theorem gnomonicCoordinates_gnomonicChart (p : Space n) :
    gnomonicCoordinates (gnomonicChart p) = p := by
  apply PiLp.ext
  intro i
  exact gnomonicChart_coordinate_ratio p i

theorem northLift_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    northLift (gnomonicCoordinates w) = ((w:Space (n+1)) 0)⁻¹ • (w:Space (n+1)) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [northLift_zero,PiLp.smul_apply,smul_eq_mul]
    exact (inv_mul_cancel₀ hw.ne').symm
  · simp only [northLift_succ,gnomonicCoordinates_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

theorem gnomonicChart_gnomonicCoordinates (w : Sphere (n+1))
    (hw : 0 < (w:Space (n+1)) 0) :
    gnomonicChart (gnomonicCoordinates w) = w := by
  apply Subtype.ext
  change ‖northLift (gnomonicCoordinates w)‖⁻¹ • northLift (gnomonicCoordinates w) = _
  rw [northLift_gnomonicCoordinates w hw,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw),sphere_norm,mul_one,inv_inv,smul_smul]
  rw [mul_inv_cancel₀ hw.ne',one_smul]

theorem northLift_distance (p q : Space n) : dist (northLift p) (northLift q) = dist p q := by
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [dist_eq_norm,dist_eq_norm,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  simp only [PiLp.sub_apply,northLift_zero,northLift_succ,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add]

theorem gnomonicChart_distance_le (p q : Space n) :
    dist (gnomonicChart p) (gnomonicChart q) ≤ 2*dist p q := by
  have hp : 1 ≤ ‖northLift p‖ := by
    have he := northLift_norm_sq p
    nlinarith [norm_nonneg (northLift p),sq_nonneg ‖p‖]
  have hh := normalize_dist_le_twice hp (northLift_ne_zero q)
  simpa only [Subtype.dist_eq,NormedSpace.normalize,gnomonicChart,northLift_distance] using hh

end Falconer

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

noncomputable def gnomonicRatio {n : ℕ} (z : Space (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.succ/z 0)

@[simp] theorem gnomonicRatio_apply {n : ℕ} (z : Space (n+1)) (i : Fin n) :
    gnomonicRatio z i = z i.succ/z 0 := rfl

theorem gnomonicRatio_continuousOn (n : ℕ) :
    ContinuousOn (@gnomonicRatio n) {z | z 0 ≠ 0} := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  exact (EuclideanSpace.proj i.succ).continuous.continuousOn.div
    (EuclideanSpace.proj 0).continuous.continuousOn (fun z hz => hz)

theorem northLift_gnomonicRatio {n : ℕ} (z : Space (n+1)) (hz : z 0 ≠ 0) :
    northLift (gnomonicRatio z) = (z 0)⁻¹ • z := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hz]
  · simp only [northLift_succ,gnomonicRatio_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring

@[simp] theorem gnomonicRatio_chart {n : ℕ} (x : Space n) :
    gnomonicRatio (gnomonicChart x) = x := by
  apply PiLp.ext
  intro i
  exact gnomonicChart_coordinate_ratio x i

theorem northLift_ratio_norm {n : ℕ} (w : Sphere (n+1))
    (hw : 0 < (w : Space (n+1)) 0) :
    ‖northLift (gnomonicRatio (w : Space (n+1)))‖ = ((w : Space (n+1)) 0)⁻¹ := by
  have he := northLift_gnomonicRatio (w : Space (n+1)) hw.ne'
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw)]
  rw [sphere_norm,mul_one]

theorem gnomonicChart_ratio {n : ℕ} (w : Sphere (n+1)) (hw : w ∈ northHemisphere n) :
    gnomonicChart (gnomonicRatio (w : Space (n+1))) = w := by
  have hw0 : 0 < (w : Space (n+1)) 0 := hw
  have he := northLift_gnomonicRatio (w : Space (n+1)) hw0.ne'
  have hn := northLift_ratio_norm w hw0
  apply Subtype.ext
  change ‖northLift (gnomonicRatio (w : Space (n+1)))‖⁻¹ •
    northLift (gnomonicRatio (w : Space (n+1))) = (w : Space (n+1))
  rw [hn,he,inv_inv,smul_smul,mul_inv_cancel₀ hw0.ne',one_smul]

theorem gnomonicChart_range (n : ℕ) : Set.range (@gnomonicChart n) = northHemisphere n := by
  apply Set.Subset.antisymm
  · rintro w ⟨x,rfl⟩
    exact gnomonicChart_mem_hemisphere x
  · intro w hw
    exact ⟨gnomonicRatio w,gnomonicChart_ratio w hw⟩

theorem gnomonicChart_measurableEmbedding (n : ℕ) : MeasurableEmbedding (@gnomonicChart n) :=
  (gnomonicChart_continuous n).measurableEmbedding (gnomonicChart_injective n)

noncomputable def gnomonicConePoint {n : ℕ} (r : ℝ) (x : Space n) : Space (n+1) :=
  r • northLift x

@[simp] theorem gnomonicConePoint_zero {n : ℕ} (r : ℝ) (x : Space n) :
    gnomonicConePoint r x 0 = r := by simp [gnomonicConePoint]

@[simp] theorem gnomonicConePoint_succ {n : ℕ} (r : ℝ) (x : Space n) (i : Fin n) :
    gnomonicConePoint r x i.succ = r*x i := by simp [gnomonicConePoint]

theorem gnomonicRatio_conePoint {n : ℕ} (r : ℝ) (hr : r ≠ 0) (x : Space n) :
    gnomonicRatio (gnomonicConePoint r x) = x := by
  apply PiLp.ext
  intro i
  simp [hr]

theorem gnomonicConePoint_radius {n : ℕ} (r : ℝ) (x : Space n) :
    gnomonicConePoint r x = (r*‖northLift x‖) • (gnomonicChart x : Space (n+1)) := by
  change r • northLift x = (r*‖northLift x‖) • (‖northLift x‖⁻¹ • northLift x)
  rw [smul_smul,mul_inv_cancel_right₀ (norm_ne_zero_iff.mpr (northLift_ne_zero x))]

end Falconer

end OAI
