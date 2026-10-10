import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Caps.Caps
import OAI.Geometry.CylinderCovering.Radial.Riemann
import OAI.Geometry.CylinderCovering.Radial.PartitionCover

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace CylinderCovering.HalfheightFinite

lemma halfwidth_nonneg (N : ℕ) : 0 ≤ halfwidth N := by
  unfold halfwidth
  positivity

lemma midpoint_distance {N : ℕ} (i : Fin N) {r : ℝ}
    (hr : r ∈ RadialRiemann.cell (-1) 1 N i) :
    |r - midpoint N i| ≤ halfwidth N := by
  have hs := RadialRiemann.point_succ (-1) 1 N (i : ℕ)
  change RadialRiemann.point (-1) 1 N i ≤ r ∧
    r ≤ RadialRiemann.point (-1) 1 N (i+1) at hr
  have hd : RadialRiemann.step (-1) 1 N = 2 * halfwidth N := by
    unfold RadialRiemann.step halfwidth
    ring
  rw [hd] at hs
  unfold midpoint
  apply abs_le.mpr
  constructor <;> linarith [hr.1, hr.2]

lemma intercept_mem {ρ e M m r u σ : ℝ}
    (hρ : 0 ≤ ρ) (he : 0 ≤ e) (hu : 0 ≤ u) (huM : u ≤ M)
    (hr : |r-m| ≤ ρ) (hσ : |σ| ≤ e) :
    (u+σ, u*r+σ*(r+m)/2) ∈ RadialFootprints.halfheightFootprint ρ e M m := by
  have hs := abs_le.mp hσ
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  have hid : u*r+σ*(r+m)/2-m*(u+σ) = (r-m)*(u+σ/2) := by ring
  change |u*r+σ*(r+m)/2-m*(u+σ)| ≤ ρ*(u+σ+2*e)
  rw [hid, abs_mul]
  have hb : |u+σ/2| ≤ u+e/2 := by
    calc
      |u+σ/2| ≤ |u|+|σ/2| := abs_add_le _ _
      _ = u+|σ|/2 := by rw [abs_of_nonneg hu, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      _ ≤ u+e/2 := by linarith
  calc
    |r-m| * |u+σ/2| ≤ ρ*(u+e/2) :=
      mul_le_mul hr hb (abs_nonneg _) hρ
    _ ≤ ρ*(u+σ+2*e) := mul_le_mul_of_nonneg_left (by linarith) hρ

lemma firstRaw_ne (δ r : ℝ) : firstRaw δ r ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 0) h
  norm_num [firstRaw] at this

lemma secondRaw_ne (δ r : ℝ) : secondRaw δ r ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 1) h
  norm_num [secondRaw] at this

lemma normalized_cylinder_mem {v z q : Space} {F : Set Space}
    (hv : v ≠ 0) (hq : q ∈ F) (t : ℝ) (hz : z = q+t • v) :
    z ∈ RadialSweep.cylinder (‖v‖⁻¹ • v)
      (TriangularCovering.projection (‖v‖⁻¹ • v) '' F) := by
  let a : Space := ‖v‖⁻¹ • v
  have hnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hva : ‖v‖ • a = v := by
    dsimp [a]
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  refine ⟨TriangularCovering.projection a q, ⟨q,hq,rfl⟩,
    inner ℝ a q+t*‖v‖, ?_⟩
  change z = (q-(inner ℝ a q) • a)+(inner ℝ a q+t*‖v‖) • a
  rw [add_smul, mul_smul, hva]
  rw [hz]
  abel

lemma first_intercept (δ r m u X : ℝ) :
    point X (u*r+δ*X*alpha r) (u+δ*X*beta r) =
      firstFoot (u+δ*X*(r-m)/2,
        u*r+(δ*X*(r-m)/2)*(r+m)/2) + (X/2) • firstRaw δ m := by
  ext i
  fin_cases i <;> simp [point, firstFoot, firstRaw, alpha, beta] <;> ring

lemma second_intercept (δ s m v Y : ℝ) :
    point (v*s-δ*Y*alpha s) Y (1-v+δ*Y*beta s) =
      secondFoot (v+(-δ*Y*(s-m)/2),
        v*s+(-δ*Y*(s-m)/2)*(s+m)/2) + (Y/2) • secondRaw δ m := by
  ext i
  fin_cases i <;> simp [point, secondFoot, secondRaw, alpha, beta] <;> ring

lemma first_member {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {r u X : ℝ} (hr : r ∈ RadialRiemann.cell (-1) 1 N i)
    (hu : 0 ≤ u) (huR : u ≤ R r) (hX : |X| ≤ 1) :
    point X (u*r+δ*X*alpha r) (u+δ*X*beta r) ∈
      RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ R N i) := by
  have hdist := midpoint_distance i hr
  have hs : |δ*X*(r-midpoint N i)/2| ≤ collar δ N := by
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hδ]
    norm_num
    have hm := mul_le_mul hX hdist (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    unfold collar
    nlinarith
  have huM : u ≤ maxCap R N i := huR.trans
    (RadialRiemann.le_capMax (by norm_num) hR hr)
  have hm := intercept_mem (halfwidth_nonneg N)
    (show 0 ≤ collar δ N by unfold collar halfwidth; positivity) hu huM hdist hs
  apply normalized_cylinder_mem (firstRaw_ne δ (midpoint N i))
    (show firstFoot (u+δ*X*(r-midpoint N i)/2,
      u*r+(δ*X*(r-midpoint N i)/2)*(r+midpoint N i)/2) ∈ firstFoot '' foot δ R N i from
      ⟨_,hm,rfl⟩) (X/2)
  exact first_intercept δ r (midpoint N i) u X

lemma second_member {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1)) {N : ℕ} (i : Fin N)
    {s v Y : ℝ} (hs : s ∈ RadialRiemann.cell (-1) 1 N i)
    (hv : 0 ≤ v) (hvR : v ≤ R s) (hY : |Y| ≤ 1) :
    point (v*s-δ*Y*alpha s) Y (1-v+δ*Y*beta s) ∈
      RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ R N i) := by
  have hdist := midpoint_distance i hs
  have hσ : |-δ*Y*(s-midpoint N i)/2| ≤ collar δ N := by
    rw [abs_div, abs_mul, abs_mul, abs_neg, abs_of_nonneg hδ]
    norm_num
    have hm := mul_le_mul hY hdist (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    unfold collar
    nlinarith
  have hvM : v ≤ maxCap R N i := hvR.trans
    (RadialRiemann.le_capMax (by norm_num) hR hs)
  have hm := intercept_mem (halfwidth_nonneg N)
    (show 0 ≤ collar δ N by unfold collar halfwidth; positivity) hv hvM hdist hσ
  apply normalized_cylinder_mem (secondRaw_ne δ (midpoint N i))
    (show secondFoot (v+(-δ*Y*(s-midpoint N i)/2),
      v*s+(-δ*Y*(s-midpoint N i)/2)*(s+midpoint N i)/2) ∈ secondFoot '' foot δ R N i from
      ⟨_,hm,rfl⟩) (Y/2)
  exact second_intercept δ s (midpoint N i) v Y

theorem finite_coverage {δ : ℝ} (hδ : 0 ≤ δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1:ℝ) 1))
    (hcover : HalfHeightCaps.Covered δ R) {N : ℕ} (hN : 0<N) :
    ∀ z ∈ tetrahedron,
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ R N i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ R N i)) := by
  rintro z ⟨X,Y,Z,hX,hY,rfl⟩
  have hX1 : |X| ≤ 1 := by linarith [abs_nonneg Y]
  have hY1 : |Y| ≤ 1 := by linarith [abs_nonneg X]
  rcases hcover X Y Z hX hY with ⟨r,u,hr,hu,huR,hYr,hZr⟩ |
    ⟨s,v,hs,hv,hvR,hXs,hZs⟩
  · obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN (abs_le.mp hr)
    left
    refine ⟨i,?_⟩
    change Y = u*r+δ*X*alpha r at hYr
    change Z = u+δ*X*beta r at hZr
    rw [hYr,hZr]
    exact first_member hδ hR i hi hu huR hX1
  · obtain ⟨i,hi⟩ := RadialRiemann.exists_cell hN (abs_le.mp hs)
    right
    refine ⟨i,?_⟩
    change X = v*s-δ*Y*alpha s at hXs
    change 1-Z = v-δ*Y*beta s at hZs
    have hZ : Z = 1-v+δ*Y*beta s := by linarith
    rw [hXs,hZ]
    exact second_member hδ hR i hi hv hvR hY1

lemma firstAxis_unit (δ r : ℝ) : ‖firstAxis δ r‖ = 1 := by
  unfold firstAxis
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (firstRaw_ne δ r))]

lemma secondAxis_unit (δ r : ℝ) : ‖secondAxis δ r‖ = 1 := by
  unfold secondAxis
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (secondRaw_ne δ r))]

theorem cubic_finite_coverage {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0<N) :
    ∀ z ∈ tetrahedron,
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ (cubicCap δ) N i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ (cubicCap δ) N i)) := by
  apply finite_coverage hδ.le (by unfold cubicCap profile; fun_prop) _ hN
  exact HalfHeightCaps.cubic_covers hδ

theorem fractional_finite_coverage {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1)
    {N : ℕ} (hN : 0<N) :
    ∀ z ∈ tetrahedron,
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (firstAxis δ (midpoint N i)) (firstBase δ (fractionalCap δ) N i)) ∨
      (∃ i : Fin N, z ∈ RadialSweep.cylinder (secondAxis δ (midpoint N i)) (secondBase δ (fractionalCap δ) N i)) := by
  apply finite_coverage hδ.le (by unfold fractionalCap profile; fun_prop) _ hN
  exact HalfHeightCaps.fractional_covers hδ hsmall

end CylinderCovering.HalfheightFinite

end

end OAI
