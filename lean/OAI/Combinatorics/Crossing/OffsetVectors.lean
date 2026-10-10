import OAI.Combinatorics.Crossing.PlanarDeterminant

namespace OAI

noncomputable section
namespace Zarankiewicz

def rotateQuarter (v : Plane) : Plane := (-v.2,v.1)
def squaredLength (v : Plane) : ℝ := v.1^2+v.2^2

theorem squaredLength_pos (v : Plane) (hv : v ≠ 0) : 0 < squaredLength v := by
  have hx := sq_nonneg v.1
  have hy := sq_nonneg v.2
  have hnon : 0 ≤ squaredLength v := by dsimp [squaredLength]; linarith
  rcases eq_or_lt_of_le hnon with hzero | hpos
  · have h₁ : v.1=0 := by dsimp [squaredLength] at hzero; nlinarith
    have h₂ : v.2=0 := by dsimp [squaredLength] at hzero; nlinarith
    exact False.elim (hv (Prod.ext h₁ h₂))
  · exact hpos

def normalShift (v : Plane) : Plane := (squaredLength v)⁻¹ • rotateQuarter v

theorem det2_normalShift (v : Plane) (hv : v ≠ 0) : det2 v (normalShift v) = 1 := by
  have hn := ne_of_gt (squaredLength_pos v hv)
  unfold normalShift
  rw [det2_smul_right]
  have he : det2 v (rotateQuarter v) = squaredLength v := by
    dsimp [det2,rotateQuarter,squaredLength]
    ring
  rw [he,inv_mul_cancel₀ hn]

def cornerShift (u v : Plane) : Plane := (det2 u v)⁻¹ • (v-u)

theorem det2_cornerShift_left (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 u (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,sub_zero,inv_mul_cancel₀ hn]

theorem det2_cornerShift_right (u v : Plane) (hn : det2 u v ≠ 0) :
    det2 v (cornerShift u v) = 1 := by
  unfold cornerShift
  rw [det2_smul_right,det2_sub_right,det2_self,det2_swap u v,zero_sub,neg_neg,inv_mul_cancel₀ hn]

end Zarankiewicz

end

end OAI
