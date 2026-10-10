import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff

def sourceMesh (t r : ℝ) : ℕ := 2*⌈t/r^2⌉₊
def sourceStep (t r : ℝ) : ℝ := t/(⌈t/r^2⌉₊:ℝ)

lemma sourceMesh_properties {t r : ℝ} (ht : 0<t) (hr : 0<r) :
    0<sourceMesh t r ∧ 0<sourceStep t r ∧ sourceStep t r≤r^2 ∧
      (sourceMesh t r:ℝ)*sourceStep t r=2*t := by
  have hq : 0<t/r^2 := by positivity
  have hn : 0<⌈t/r^2⌉₊ := Nat.ceil_pos.mpr hq
  have hn' : 0<(⌈t/r^2⌉₊:ℝ) := by exact_mod_cast hn
  refine ⟨Nat.mul_pos (by norm_num) hn,by dsimp [sourceStep]; positivity,?_,?_⟩
  · change t/(⌈t/r^2⌉₊:ℝ)≤r^2
    apply (div_le_iff₀ hn').mpr
    have h := Nat.le_ceil (t/r^2)
    have hh := (div_le_iff₀ (sq_pos_of_pos hr)).mp h
    linarith
  · dsimp [sourceMesh,sourceStep]
    push_cast
    field_simp

lemma sourceMesh_bounds {t r D αmin αmax : ℝ}
    (ht : 0<t) (hr : 0<r) (hD : 1≤D) (hαmin : 0<αmin)
    (hl : αmin≤D*r) (hu : D*r≤αmax) :
    (2*t/αmax^2)*D^2≤(sourceMesh t r:ℝ) ∧
    (sourceMesh t r:ℝ)≤(2*t/αmin^2+2)*D^2 := by
  have hDp : 0<D := by linarith
  have hαmax : 0<αmax := hαmin.trans_le (hl.trans hu)
  have hsq₁ : αmin^2≤D^2*r^2 := by nlinarith [sq_nonneg (D*r-αmin)]
  have hsq₂ : D^2*r^2≤αmax^2 := by nlinarith [sq_nonneg (αmax-D*r)]
  have hlo' : (t/αmax^2)*D^2≤t/r^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      _ = t*(D^2*r^2)/αmax^2 := by ring
      _ ≤ t*αmax^2/αmax^2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq₂ ht.le) (sq_nonneg _)
      _ = t := by field_simp
  have hhi : t/r^2≤(t/αmin^2)*D^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    have hh : t*αmin^2≤t*(D^2*r^2) := mul_le_mul_of_nonneg_left hsq₁ ht.le
    have hh' := (le_div_iff₀ (sq_pos_of_pos hαmin)).mpr hh
    convert hh' using 1; ring
  have hnlo := Nat.le_ceil (t/r^2)
  have hnhi := (Nat.ceil_lt_add_one (show 0≤t/r^2 by positivity)).le
  simp only [sourceMesh,Nat.cast_mul,Nat.cast_ofNat]
  have hDsq : 1≤D^2 := by nlinarith
  constructor
  · calc
      _ = 2*((t/αmax^2)*D^2) := by ring
      _ ≤ 2*(⌈t/r^2⌉₊:ℝ) := mul_le_mul_of_nonneg_left (hlo'.trans hnlo) (by norm_num)
  · calc
      _ ≤ 2*(t/r^2+1) := mul_le_mul_of_nonneg_left hnhi (by norm_num)
      _ ≤ 2*((t/αmin^2)*D^2+D^2) := by gcongr
      _ = _ := by ring
end HardSphere.PathCutoff

end
end

end

end OAI
