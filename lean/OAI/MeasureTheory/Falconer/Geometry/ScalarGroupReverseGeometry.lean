import OAI.MeasureTheory.Falconer.Geometry.ScalarGroupGeometry

namespace OAI

/-! Coefficient bounds needed when reversing the two child families. -/
namespace Falconer
 theorem scalar_group_index_near_three {η δ r b x y u v z w : ℝ} {j k q : ℤ}
    (hη : 0 < η) (hδ : 0 < δ) (hδr : δ ≤ 3*r) (hrη : 10*r ≤ η)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 3)
    (hx : ⌊(x-z)/η⌋ = k) (hy : ⌊(y-w)/η⌋ = j)
    (hu : |u-x| ≤ r) (hv : |v-y| ≤ r)
    (hq : ⌊(u+b*v)/δ⌋ = q) :
    k ∈ Finset.Icc (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋-8)
      (⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋+8) := by
  have hx0 := Int.floor_le ((x-z)/η)
  have hx1 := Int.lt_floor_add_one ((x-z)/η)
  have hy0 := Int.floor_le ((y-w)/η)
  have hy1 := Int.lt_floor_add_one ((y-w)/η)
  rw [hx] at hx0 hx1
  rw [hy] at hy0 hy1
  have hxlo : (k:ℝ)*η ≤ x-z := (le_div_iff₀ hη).1 hx0
  have hxhi : x-z < ((k:ℝ)+1)*η := (div_lt_iff₀ hη).1 hx1
  have hylo : (j:ℝ)*η ≤ y-w := (le_div_iff₀ hη).1 hy0
  have hyhi : y-w < ((j:ℝ)+1)*η := (div_lt_iff₀ hη).1 hy1
  have hyres0 : 0 ≤ y-(w+(j:ℝ)*η) := by linarith
  have hyres1 : y-(w+(j:ℝ)*η) ≤ η := by linarith
  have hbys := mul_le_mul hb1 hyres1 hyres0 (by norm_num : (0:ℝ) ≤ 3)
  have hby0 := mul_nonneg hb0 hyres0
  rw [abs_le] at hu hv
  have hbvr := mul_le_mul_of_nonneg_left hv.2 hb0
  have hbvl := mul_le_mul_of_nonneg_left hv.1 hb0
  have hbr := mul_le_mul_of_nonneg_right hb1 (by linarith : 0 ≤ r)
  have hq0 := Int.floor_le ((u+b*v)/δ)
  have hq1 := Int.lt_floor_add_one ((u+b*v)/δ)
  rw [hq] at hq0 hq1
  have hqlo : (q:ℝ)*δ ≤ u+b*v := (le_div_iff₀ hδ).1 hq0
  have hqhi : u+b*v < ((q:ℝ)+1)*δ := (div_lt_iff₀ hδ).1 hq1
  let t : ℝ := ((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η
  have ht : t*η = (q:ℝ)*δ-z-b*(w+(j:ℝ)*η) := by
    dsimp [t]; field_simp
  have hl := Int.floor_le t
  have hh := Int.lt_floor_add_one t
  have hfl := mul_le_mul_of_nonneg_right hl hη.le
  have hfh := mul_lt_mul_of_pos_right hh hη
  have hkl : (⌊t⌋:ℝ)-8 ≤ (k:ℝ) := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  have hku : (k:ℝ) ≤ (⌊t⌋:ℝ)+8 := by
    apply (mul_le_mul_iff_right₀ hη).1
    nlinarith
  apply Finset.mem_Icc.mpr
  dsimp only [t] at hkl hku
  constructor
  · exact_mod_cast hkl
  · exact_mod_cast hku

 theorem scalar_group_reverse_index_near {η δ r b x y u v z w : ℝ} {j k q : ℤ}
    (hη : 0 < η) (hδ : 0 < δ) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 1/3 ≤ b)
    (hx : ⌊(x-z)/η⌋ = j) (hy : ⌊(y-w)/η⌋ = k)
    (hu : |u-x| ≤ r) (hv : |v-y| ≤ r)
    (hq : ⌊(u+b*v)/δ⌋ = q) :
    k ∈ Finset.Icc (⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋-8)
      (⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋+8) := by
  have hb : 0 < b := by linarith
  have hr : 0 ≤ r := hδ.le.trans hδr
  have hi : 1/b ≤ (3:ℝ) := (div_le_iff₀ hb).2 (by linarith)
  have hd : δ/b ≤ 3*r := (div_le_iff₀ hb).2 (by nlinarith)
  have hid : (v+(1/b)*u)/(δ/b) = (u+b*v)/δ := by
    field_simp
    ring
  have hq' : ⌊(v+(1/b)*u)/(δ/b)⌋ = q := by rw [hid]; exact hq
  exact scalar_group_index_near_three hη (div_pos hδ hb) hd hrη
    (one_div_nonneg.mpr hb.le) hi hy hx hv hu hq'

end Falconer

end OAI
