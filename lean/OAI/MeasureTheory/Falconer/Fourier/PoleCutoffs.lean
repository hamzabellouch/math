import OAI.MeasureTheory.Falconer.Angular.SmoothCapPartition
import OAI.MeasureTheory.Falconer.Geometry.QuadraticChart
import OAI.MeasureTheory.Falconer.Graphs.AllDimensionalGraphGeometry
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! # The actual north, south, and off-pole partition

The fixed ambient bumps have outer radius 1/4 and are one on radius 1/8.
The remainder therefore stays a fixed distance from both stationary poles.
-/

namespace Falconer
open Set Metric
open scoped ContDiff

def oppositePole {d : ℕ} (e : Sphere d) : Sphere d :=
  ⟨-(e : Space d), by simpa only [mem_sphere,dist_zero_right,norm_neg] using e.property⟩

@[simp] theorem oppositePole_coe {d : ℕ} (e : Sphere d) :
    (oppositePole e : Space d) = -(e : Space d) := rfl

@[simp] theorem oppositePole_opposite {d : ℕ} (e : Sphere d) :
    oppositePole (oppositePole e) = e := by ext; simp

noncomputable def poleCutoff {d : ℕ} (e : Sphere d) : Space d → ℝ :=
  capBump (1/4) (by norm_num) e

noncomputable def offPoleCutoff {d : ℕ} (e : Sphere d) (x : Space d) : ℝ :=
  1-poleCutoff e x-poleCutoff (oppositePole e) x

theorem poleCutoff_contDiff {d : ℕ} (e : Sphere d) : ContDiff ℝ ∞ (poleCutoff e) :=
  (capBump (1/4) (by norm_num) e).contDiff

theorem offPoleCutoff_contDiff {d : ℕ} (e : Sphere d) :
    ContDiff ℝ ∞ (offPoleCutoff e) :=
  (contDiff_const.sub (poleCutoff_contDiff e)).sub (poleCutoff_contDiff _)

theorem poleCutoff_one {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : ‖x-(e : Space d)‖ ≤ 1/8) : poleCutoff e x = 1 := by
  apply (capBump (1/4) (by norm_num) e).one_of_mem_closedBall
  change dist x (e : Space d) ≤ (1/4 : ℝ)/2
  rw [dist_eq_norm]
  convert hx using 1
  norm_num

theorem poleCutoff_zero {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : 1/4 ≤ ‖x-(e : Space d)‖) : poleCutoff e x = 0 := by
  apply (capBump (1/4) (by norm_num) e).zero_of_le_dist
  simpa only [dist_eq_norm,capBump] using hx

theorem poleCutoff_support {d : ℕ} (e : Sphere d) (x : Space d)
    (hx : poleCutoff e x ≠ 0) : ‖x-(e : Space d)‖ < 1/4 := by
  by_contra h
  exact hx (poleCutoff_zero e x (le_of_not_gt h))

private theorem pole_distance_sum {d : ℕ} (e w : Sphere d) :
    2 ≤ ‖(w : Space d)-(e : Space d)‖ +
      ‖(w : Space d)-(oppositePole e : Space d)‖ := by
  have htwo : ‖(e : Space d)-(oppositePole e : Space d)‖ = 2 := by
    rw [oppositePole_coe,sub_neg_eq_add,← two_smul ℝ,norm_smul,sphere_norm]
    norm_num
  have h := norm_sub_le_norm_sub_add_norm_sub (e : Space d) (w : Space d)
    (oppositePole e : Space d)
  rwa [htwo,norm_sub_rev (e : Space d) (w : Space d)] at h

theorem offPoleCutoff_zero_near {d : ℕ} (e w : Sphere d)
    (hw : ‖(w : Space d)-(e : Space d)‖ ≤ 1/8) : offPoleCutoff e w = 0 := by
  have hs := pole_distance_sum e w
  have ho : poleCutoff (oppositePole e) w = 0 := poleCutoff_zero _ _ (by linarith)
  simp only [offPoleCutoff,poleCutoff_one e w hw,ho,sub_self]

theorem offPoleCutoff_opposite {d : ℕ} (e : Sphere d) :
    offPoleCutoff (oppositePole e) = offPoleCutoff e := by
  funext x
  simp only [offPoleCutoff,oppositePole_opposite]
  ring

theorem offPoleCutoff_gap {d : ℕ} (e w : Sphere d) (hw : offPoleCutoff e w ≠ 0) :
    (1 : ℝ)/16 ≤ ‖perpendicularPart (w : Space d) (e : Space d)‖ := by
  have hp : 1/8 < ‖(w : Space d)-(e : Space d)‖ := by
    by_contra h
    exact hw (offPoleCutoff_zero_near e w (le_of_not_gt h))
  have hm : 1/8 < ‖(w : Space d)-(oppositePole e : Space d)‖ := by
    by_contra h
    have hz := offPoleCutoff_zero_near (oppositePole e) w (le_of_not_gt h)
    rw [offPoleCutoff_opposite] at hz
    exact hw hz
  have hps := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/8) (norm_nonneg _)).mpr hp
  have hms := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 1/8) (norm_nonneg _)).mpr hm
  simp only [oppositePole_coe] at hms
  have hplus := norm_sub_sq_real (w : Space d) (e : Space d)
  have hminus := norm_sub_sq_real (w : Space d) (oppositePole e : Space d)
  rw [sphere_norm,sphere_norm] at hplus hminus
  rw [oppositePole_coe,inner_neg_right] at hminus
  let t := inner ℝ (w : Space d) (e : Space d)
  have ht₁ : 0 ≤ 127/128-t := by dsimp [t]; nlinarith
  have ht₂ : 0 ≤ 127/128+t := by dsimp [t]; nlinarith
  have ht := mul_nonneg ht₁ ht₂
  have hsq : ‖perpendicularPart (w : Space d) (e : Space d)‖^2 = 1-t^2 := by
    have hh := norm_sub_sq_real (e : Space d) (t • (w : Space d))
    rw [norm_smul,sphere_norm,sphere_norm,Real.norm_eq_abs,mul_one,
      sq_abs,real_inner_smul_right] at hh
    have hi : inner ℝ (e : Space d) (w : Space d) = t := by
      dsimp [t]
      exact real_inner_comm _ _
    rw [hi] at hh
    change ‖perpendicularPart (w : Space d) (e : Space d)‖^2 = _
    dsimp only [perpendicularPart]
    dsimp only [t] at hh ⊢
    nlinarith
  nlinarith [norm_nonneg (perpendicularPart (w : Space d) (e : Space d))]

theorem poleCutoff_partition {d : ℕ} (e : Sphere d) (x : Space d) :
    poleCutoff e x+poleCutoff (oppositePole e) x+offPoleCutoff e x = 1 := by
  dsimp [offPoleCutoff]
  ring

/-- In quadratic coordinates, Euclidean distance from the pole is exactly
the coordinate radius. This gives the needed interior cutoff support. -/
theorem quadraticSpherePoint_dist_pole {n : ℕ} {u : Space n} (hu : ‖u‖ ≤ 2) :
    ‖quadraticSpherePoint u-coordinateJoin (0 : Space n) 1‖ = ‖u‖ := by
  have hp : ‖coordinateJoin (0 : Space n) 1‖ = 1 := by
    have h := coordinateJoin_norm_sq (0 : Space n) 1
    simp only [norm_zero,zero_pow (by decide : 2 ≠ 0),one_pow] at h
    nlinarith [norm_nonneg (coordinateJoin (0 : Space n) 1)]
  have h := norm_sub_sq_real (quadraticSpherePoint u) (coordinateJoin (0 : Space n) 1)
  rw [quadraticSpherePoint_norm hu,hp,quadraticSpherePoint_phase] at h
  nlinarith [norm_nonneg (quadraticSpherePoint u-coordinateJoin (0 : Space n) 1),norm_nonneg u]

/-- Only a small fixed part of the coordinate image is needed for the
application. Radial continuity proves its inclusion without imposing a
global inverse chart. -/
theorem quadraticToGnomonic_image_smallBall {n : ℕ} (x : Space n)
    (hx : ‖x‖ ≤ 1/2) :
    x ∈ quadraticToGnomonic '' ball (0 : Space n) 1 := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0,by simp,by simp [quadraticToGnomonic]⟩
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let g : ℝ → ℝ := fun r => Real.sqrt (1-r^2/4)/(1-r^2/2)*r
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul _ continuousOn_id
    apply ContinuousOn.div
    · exact (continuousOn_const.sub ((continuousOn_id.pow 2).div_const 4)).sqrt
    · exact continuousOn_const.sub ((continuousOn_id.pow 2).div_const 2)
    · intro r hr
      have hr2 : r^2 ≤ 1 := by
        simpa using (sq_le_sq₀ hr.1 (by norm_num : (0 : ℝ) ≤ 1)).mpr hr.2
      linarith
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : 1 ≤ g 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/4)
    have hn := Real.sqrt_nonneg (3/4 : ℝ)
    have he : g 1 = 2*Real.sqrt (3/4 : ℝ) := by dsimp [g]; norm_num; ring
    rw [he]
    nlinarith
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hg
    (show ‖x‖ ∈ Icc (g 0) (g 1) from ⟨by rw [hg0]; exact hxn.le,hx.trans (by linarith)⟩)
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hr.2
    intro hrEq
    have he1 : g 1 = ‖x‖ := by simpa only [hrEq] using he
    linarith
  let u : Space n := (r/‖x‖) • x
  have hu : ‖u‖ = r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hr.1 hxn.le),div_mul_cancel₀ _ hxn.ne']
  refine ⟨u,by simpa only [mem_ball,dist_zero_right,hu] using hr1,?_⟩
  change (Real.sqrt (1-‖u‖^2/4)/(1-‖u‖^2/2)) • u = x
  rw [hu]
  change (Real.sqrt (1-r^2/4)/(1-r^2/2)) • ((r/‖x‖) • x) = x
  rw [smul_smul]
  have hc : (Real.sqrt (1-r^2/4)/(1-r^2/2))*(r/‖x‖) = 1 := by
    apply (mul_right_cancel₀ hxn.ne')
    calc
      _ = (Real.sqrt (1-r^2/4)/(1-r^2/2))*r := by field_simp
      _ = ‖x‖ := he
      _ = 1*‖x‖ := (one_mul _).symm
  rw [hc,one_smul]

end Falconer

end OAI
