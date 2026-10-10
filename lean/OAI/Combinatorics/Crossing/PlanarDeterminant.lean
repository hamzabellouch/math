import OAI.Combinatorics.Crossing.PlanarSegments

namespace OAI

namespace Zarankiewicz

theorem det2_add_left (u v w : Plane) : det2 (u+v) w = det2 u w+det2 v w := by
  dsimp [det2]
  ring

theorem det2_add_right (u v w : Plane) : det2 u (v+w) = det2 u v+det2 u w := by
  dsimp [det2]
  ring

theorem det2_sub_left (u v w : Plane) : det2 (u-v) w = det2 u w-det2 v w := by
  dsimp [det2]
  ring

theorem det2_sub_right (u v w : Plane) : det2 u (v-w) = det2 u v-det2 u w := by
  dsimp [det2]
  ring

theorem det2_smul_left (r : ℝ) (u v : Plane) : det2 (r • u) v = r*det2 u v := by
  dsimp [det2]
  ring

theorem det2_smul_right (r : ℝ) (u v : Plane) : det2 u (r • v) = r*det2 u v := by
  dsimp [det2]
  ring

@[simp] theorem det2_self (u : Plane) : det2 u u = 0 := by
  dsimp [det2]
  ring

@[simp] theorem det2_zero_left (u : Plane) : det2 0 u = 0 := by simp [det2]
@[simp] theorem det2_zero_right (u : Plane) : det2 u 0 = 0 := by simp [det2]

end Zarankiewicz

end OAI
