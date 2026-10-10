import OAI.NumberTheory.DukePrimeDegree.Entropy.CoverPredecessorPacking
import OAI.NumberTheory.DukePrimeDegree.Geometry.DistanceCutBounds

namespace OAI

/-! # Uniform comparison of neighboring exponential chart radii -/

noncomputable section
namespace DukePrimeDegree
open PrimeDegreePackets

lemma exponential_radius_adjacent {a B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    {k m : ℕ} (hkm : k ≤ m+1) :
    a*Real.exp (-B*(m:ℝ)) ≤ Real.exp B*(a*Real.exp (-B*(k:ℝ))) := by
  have hkmR : (k:ℝ) ≤ (m:ℝ)+1 := by exact_mod_cast hkm
  have he : -B*(m:ℝ) ≤ B+ -B*(k:ℝ) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) ha
  rw [Real.exp_add] at hh
  calc
    _ ≤ a*(Real.exp B*Real.exp (-B*(k:ℝ))) := hh
    _ = _ := by ring

lemma exponential_cover_scale_bounds {a B : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (k : ℕ) :
    let r := a*Real.exp (-B*(k:ℝ))
    let δ := Real.log (1+r)/8
    0 < r ∧ r ≤ a ∧ 0 < δ ∧ δ ≤ a/8 ∧ r ≤ 16*δ := by
  dsimp only
  let r := a*Real.exp (-B*(k:ℝ))
  have hr : 0 < r := mul_pos ha (Real.exp_pos _)
  have hra : r ≤ a := by
    have he : Real.exp (-B*(k:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hB (Nat.cast_nonneg (α := ℝ) k)])
    exact (mul_le_mul_of_nonneg_left he ha.le).trans_eq (mul_one a)
  have hr1 : r ≤ 1 := hra.trans ha1
  have hlogp : 0 < Real.log (1+r) := Real.log_pos (by linarith)
  have hlogle : Real.log (1+r) ≤ r := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1+r by linarith)
    linarith
  have hlogge := half_le_log_one_add hr.le hr1
  change 0 < r ∧ r ≤ a ∧ 0 < Real.log (1+r)/8 ∧
    Real.log (1+r)/8 ≤ a/8 ∧ r ≤ 16*(Real.log (1+r)/8)
  exact ⟨hr,hra,by positivity,by linarith,by linarith⟩

lemma exponential_cover_image_radius {a B : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B)
    {k m : ℕ} (hkm : k ≤ m+1) :
    a*Real.exp (-B*(m:ℝ)) ≤
      (16*Real.exp B)*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8) := by
  have hb := (exponential_cover_scale_bounds ha ha1 hB k).2.2.2.2
  calc
    _ ≤ Real.exp B*(a*Real.exp (-B*(k:ℝ))) := exponential_radius_adjacent ha.le hB hkm
    _ ≤ Real.exp B*(16*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by ring

lemma exponential_cover_smallness {n : ℕ} {a B K : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hsmall : (n:ℝ)*K*a ≤ 4) (k : ℕ) :
    (n:ℝ)*K*(Real.log (1+a*Real.exp (-B*(k:ℝ)))/8) ≤ 1/2 := by
  have hd := (exponential_cover_scale_bounds ha ha1 hB k).2.2.2.1
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg (Nat.cast_nonneg n) hK)
  nlinarith

end DukePrimeDegree

end

end OAI
