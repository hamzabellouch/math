import OAI.Geometry.NodalSets.Elliptic.HalfScaleLemmas
import OAI.Geometry.NodalSets.Waves.LatticeGeometry

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
noncomputable section

def unitDirection (v : Coord) : Coord := (‖v‖⁻¹:ℝ) • v

lemma norm_unitDirection_le (v : Coord) : ‖unitDirection v‖ ≤ 1 := by
  by_cases hv : v = 0
  · simp [unitDirection,hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [unitDirection,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  exact le_rfl

def directionalLatticeIndex (n : ℕ) (x : Coord) (K : ℝ) (v : Coord) : Fin 4 → ℤ :=
  roundedLatticeIndex n (x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v)

lemma directional_rounding_error {n : ℕ} (hn : 0 < n) (x : Coord) (K : ℝ) (v : Coord) :
    ‖scaledLatticePoint n (directionalLatticeIndex n x K v)-
      (x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v)‖ ≤ 2*(n:ℝ)^(-1/2:ℝ) :=
  (norm_le_sourceEuclideanNorm _).trans (rounded_lattice_distance hn _)

lemma directional_center_distance {n : ℕ} (hn : 0 < n) (x : Coord) (K : ℝ) (hK : 0 ≤ K) (v : Coord) :
    ‖scaledLatticePoint n (directionalLatticeIndex n x K v)-x‖ ≤ (K+2)*(n:ℝ)^(-1/2:ℝ) := by
  let z := x+(K*(n:ℝ)^(-1/2:ℝ)) • unitDirection v
  have h := norm_sub_le_norm_sub_add_norm_sub (scaledLatticePoint n (directionalLatticeIndex n x K v)) z x
  have hz : ‖z-x‖ ≤ K*(n:ℝ)^(-1/2:ℝ) := by
    simp only [z,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hK (lattice_scale_pos hn).le)]
    exact (mul_le_mul_of_nonneg_left (norm_unitDirection_le v)
      (mul_nonneg hK (lattice_scale_pos hn).le)).trans_eq (mul_one _)
  have hr := directional_rounding_error hn x K v
  dsimp [z] at h hz
  nlinarith

lemma directional_center_mem {U : Set Coord} {n : ℕ} (hn : 0 < n)
    (x : Coord) (K : ℝ) (hK : 0 ≤ K) (v : Coord)
    (hball : closedBall x ((K+2)*(n:ℝ)^(-1/2:ℝ)) ⊆ U) :
    scaledLatticePoint n (directionalLatticeIndex n x K v) ∈ U :=
  hball (by simpa only [mem_closedBall,dist_eq_norm] using directional_center_distance hn x K hK v)

end
end Yau.Geometry

end OAI
