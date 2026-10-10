import OAI.Geometry.RCD.Sobolev.RadialLocalSobolev

namespace OAI

/-! # Centered local functions have compact realizations at the same slope scale -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

theorem centered_compact_direction (p : X) {r : ℝ} (hr : 0 < r)
    (H : X → ℝ) (L : ℝ≥0) (hH : LipschitzOnWith L H (closedBall p (2*r))) :
    ∃ (v : SobolevSpace μ Q) (V : X → ℝ),
      LipschitzWith (3*L) V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp μ Q v =ᵐ[μ] V) ∧
      (∀ x, |V x| ≤ 2*r*(L:ℝ)) ∧
      (SobolevSpace.toLp μ Q v =ᵐ[μ.restrict (closedBall p r)] fun x => H x-H p) := by
  let f := fun x => H x-H p
  have hf : LipschitzOnWith L f (closedBall p (2*r)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [f,dist_sub_right] using hH.dist_le_mul x hx y hy
  let A : ℝ≥0 := ⟨2*r*(L:ℝ),by positivity⟩
  have hB : ∀ x∈closedBall p (2*r), |f x| ≤ A := by
    intro x hx
    have hh := hH.dist_le_mul x hx p (mem_closedBall_self (by positivity))
    change |H x-H p| ≤ 2*r*(L:ℝ)
    rw [Real.dist_eq] at hh
    calc
      _ ≤ (L:ℝ)*dist x p := hh
      _ ≤ (L:ℝ)*(2*r) := mul_le_mul_of_nonneg_left hx L.coe_nonneg
      _ = _ := by ring
  have hC : A*⟨r⁻¹,inv_nonneg.mpr hr.le⟩+L=3*L := by
    apply NNReal.eq
    change (2*r*(L:ℝ))*r⁻¹+(L:ℝ)=3*(L:ℝ)
    field_simp [hr.ne']; ring
  refine ⟨radialLocalSobolev μ Q p hr hf hB,fun x => radialCutoff p r x*f x,?_,
    (radialCutoff_hasCompactSupport p hr).mul_right,
    radialLocalSobolev_coe μ Q p hr hf hB,
    (radial_local_lipschitz_cutoff p hr hf hB).2,
    radialLocalSobolev_eq_on_ball μ Q p hr hf hB⟩
  rw [← hC]
  exact (radial_local_lipschitz_cutoff p hr hf hB).1

end RegularPointCoordinates

end

end OAI
