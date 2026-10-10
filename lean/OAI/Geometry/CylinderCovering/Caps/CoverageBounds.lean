import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Caps.Caps
import OAI.Geometry.CylinderCovering.Footprints.Containment
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite.CoverageLemmas

lemma firstRaw_ne_zero (δ r : ℝ) : firstRaw δ r ≠ 0 := by
  intro h
  have h0 := congrArg (fun z : Space => z 0) h
  norm_num [firstRaw] at h0

lemma secondRaw_ne_zero (δ r : ℝ) : secondRaw δ r ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : Space => z 1) h
  norm_num [secondRaw] at h1

lemma mem_projected_cylinder_of_intercept {v p z : Space} (hv : v ≠ 0)
    {S : Set Space} (hp : p ∈ S) (s : ℝ) (hz : z = p + s • v) :
    z ∈ RadialSweep.cylinder (‖v‖⁻¹ • v)
      (TriangularCovering.projection (‖v‖⁻¹ • v) '' S) := by
  let u := ‖v‖⁻¹ • v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hscale : (s * ‖v‖) • u = s • v := by
    dsimp [u]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hn, mul_one]
  refine ⟨TriangularCovering.projection u p, ⟨p, hp, rfl⟩,
    inner ℝ u p + s * ‖v‖, ?_⟩
  rw [hz, TriangularCovering.projection, add_smul, hscale]
  module

lemma halfwidth_nonneg (N : ℕ) : 0 ≤ halfwidth N := by
  unfold halfwidth
  positivity

lemma halfwidth_eq_step (N : ℕ) :
    halfwidth N = RadialRiemann.step (-1) 1 N / 2 := by
  unfold halfwidth RadialRiemann.step
  ring

lemma cell_midpoint_dist {N : ℕ} {i : Fin N} {r : ℝ}
    (hr : r ∈ RadialRiemann.cell (-1) 1 N i) :
    |r - midpoint N i| ≤ halfwidth N := by
  rw [halfwidth_eq_step, abs_le]
  have hstep := RadialRiemann.point_succ (-1) 1 N i
  unfold midpoint
  constructor <;> linarith [hr.1, hr.2]

lemma midpoint_tagged (N : ℕ) : RadialRiemann.IsTagged (-1) 1 N (midpoint N) := by
  intro i
  have hstep := RadialRiemann.point_succ (-1) 1 N i
  have hpos := RadialRiemann.step_pos (by norm_num : (-1:ℝ) < 1)
    (Nat.zero_lt_of_lt i.isLt)
  change _ ≤ midpoint N i ∧ midpoint N i ≤ _
  unfold midpoint
  constructor <;> linarith

lemma first_intercept_identity (δ r u X p : ℝ) :
    point X (u*r+δ*X*alpha r) (u+δ*X*beta r) =
      firstFoot (u+δ*X*(r-p)/2, u*r+δ*X*(r-p)*(r+p)/4) +
        (X/2) • firstRaw δ p := by
  ext j
  fin_cases j <;> simp [point, firstFoot, firstRaw, alpha, beta] <;> ring

lemma second_intercept_identity (δ r u Y p : ℝ) :
    point (u*r-δ*Y*alpha r) Y (1-u+δ*Y*beta r) =
      secondFoot (u-δ*Y*(r-p)/2, u*r-δ*Y*(r-p)*(r+p)/4) +
        (Y/2) • secondRaw δ p := by
  ext j
  fin_cases j <;> simp [point, secondFoot, secondRaw, alpha, beta] <;> ring

lemma first_intercept_mem {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {r u X : ℝ} (hr : r ∈ RadialRiemann.cell (-1) 1 N i)
    (hu : u ∈ Icc (0:ℝ) (R r)) (hX : |X| ≤ 1) :
    (u+δ*X*(r-midpoint N i)/2,
      u*r+δ*X*(r-midpoint N i)*(r+midpoint N i)/4) ∈ foot δ R N i := by
  have hd := cell_midpoint_dist hr
  have he : 0 ≤ collar δ N :=
    div_nonneg (mul_nonneg hδ (halfwidth_nonneg N)) (by norm_num)
  have hσ := FootprintContainment.halfheight_displacement hδ hX hd
  have hM : u ≤ maxCap R N i :=
    hu.2.trans (RadialRiemann.le_capMax (by norm_num) hR hr)
  have h := FootprintContainment.halfheight_trapezoid
    (halfwidth_nonneg N) he hd hu.1 hM hσ
    (v := u*r+δ*X*(r-midpoint N i)*(r+midpoint N i)/4)
    (by ring) rfl
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

lemma second_intercept_mem {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {r u Y : ℝ} (hr : r ∈ RadialRiemann.cell (-1) 1 N i)
    (hu : u ∈ Icc (0:ℝ) (R r)) (hY : |Y| ≤ 1) :
    (u-δ*Y*(r-midpoint N i)/2,
      u*r-δ*Y*(r-midpoint N i)*(r+midpoint N i)/4) ∈ foot δ R N i := by
  have hd := cell_midpoint_dist hr
  have he : 0 ≤ collar δ N :=
    div_nonneg (mul_nonneg hδ (halfwidth_nonneg N)) (by norm_num)
  have hσ : |-(δ*Y*(r-midpoint N i)/2)| ≤ collar δ N := by
    rw [abs_neg]
    exact FootprintContainment.halfheight_displacement hδ hY hd
  have hM : u ≤ maxCap R N i :=
    hu.2.trans (RadialRiemann.le_capMax (by norm_num) hR hr)
  have h := FootprintContainment.halfheight_trapezoid
    (halfwidth_nonneg N) he hd hu.1 hM hσ
    (w := u-δ*Y*(r-midpoint N i)/2)
    (v := u*r-δ*Y*(r-midpoint N i)*(r+midpoint N i)/4)
    (by ring) (by ring)
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

lemma first_point_mem_cylinder {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {r u X : ℝ} (hr : r ∈ RadialRiemann.cell (-1) 1 N i)
    (hu : u ∈ Icc (0:ℝ) (R r)) (hX : |X| ≤ 1) :
    point X (u*r+δ*X*alpha r) (u+δ*X*beta r) ∈
      RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ R N i) := by
  apply mem_projected_cylinder_of_intercept (firstRaw_ne_zero δ (midpoint N i))
    (s := X/2)
  · exact ⟨_, first_intercept_mem hδ hR i hr hu hX, rfl⟩
  · exact first_intercept_identity δ r u X (midpoint N i)

lemma second_point_mem_cylinder {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {r u Y : ℝ} (hr : r ∈ RadialRiemann.cell (-1) 1 N i)
    (hu : u ∈ Icc (0:ℝ) (R r)) (hY : |Y| ≤ 1) :
    point (u*r-δ*Y*alpha r) Y (1-u+δ*Y*beta r) ∈
      RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ R N i) := by
  apply mem_projected_cylinder_of_intercept (secondRaw_ne_zero δ (midpoint N i))
    (s := Y/2)
  · exact ⟨_, second_intercept_mem hδ hR i hr hu hY, rfl⟩
  · exact second_intercept_identity δ r u Y (midpoint N i)

theorem family_covers_of_covered {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) (hcover : HalfHeightCaps.Covered δ R)
    {N : ℕ} (hN : 0 < N) :
    ∀ z ∈ tetrahedron,
      (∃ i : Fin N, z ∈ RadialSweep.cylinder
        (firstAxis δ (midpoint N i)) (firstBase δ R N i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder
        (secondAxis δ (midpoint N i)) (secondBase δ R N i)) := by
  rintro z ⟨X,Y,Z,hX,hY,rfl⟩
  have hX1 : |X| ≤ 1 := by linarith [abs_nonneg Y]
  have hY1 : |Y| ≤ 1 := by linarith [abs_nonneg X]
  rcases hcover X Y Z hX hY with ⟨r,u,hr,hu,hRu,hYr,hZr⟩ |
    ⟨r,u,hr,hu,hRu,hXr,hZr⟩
  · obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN (abs_le.mp hr)
    left
    refine ⟨i, ?_⟩
    rw [hYr,hZr]
    exact first_point_mem_cylinder hδ hR i hi ⟨hu,hRu⟩ hX1
  · obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN (abs_le.mp hr)
    right
    refine ⟨i, ?_⟩
    have hZ : Z = 1-u+δ*Y*HalfHeightCaps.beta r := by linarith only [hZr]
    rw [hXr,hZ]
    exact second_point_mem_cylinder hδ hR i hi ⟨hu,hRu⟩ hY1

end CylinderCovering.HalfheightFinite.CoverageLemmas

end

end OAI
