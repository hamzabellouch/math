import OAI.MeasureTheory.Falconer.Recursion.RoundedProfilePieces
import OAI.MeasureTheory.Falconer.Incidence.BlockRegularization

namespace OAI

/-! Exact identification of the normalized integer grid with block depths.
This lets the rounded analytic intervals select genuine scales of the tree. -/
namespace Falconer.Regularization

theorem blockDepth_multiple {m j B : ℕ} (hj : j ≤ m) :
    blockDepth (m*B) B (m-j) = j*B := by
  dsimp only [blockDepth]
  rw [Nat.sub_mul]
  exact Nat.sub_sub_self (Nat.mul_le_mul_right B hj)

theorem normalized_blockDepth {m j B : ℕ} (hm : 0 < m) (hB : 0 < B) (hj : j ≤ m) :
    (blockDepth (m*B) B (m-j) : ℝ)/(m*B : ℕ) = (j : ℝ)/m := by
  rw [blockDepth_multiple hj]
  push_cast
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hB' : (B : ℝ) ≠ 0 := (Nat.cast_pos.mpr hB).ne'
  field_simp

theorem innerProfileCell_natural_endpoints {n : ℕ} (hn : 0 < n) (c : ℝ × ℝ)
    (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1) (hd : 0 < (innerProfileCell n c).2) :
    ∃ i j : ℕ, i < j ∧ j ≤ n ∧
      (innerProfileCell n c).1 = (i : ℝ)/(n : ℝ) ∧
      (innerProfileCell n c).1+(innerProfileCell n c).2 = (j : ℝ)/(n : ℝ) := by
  obtain ⟨i,j,hi,hij,hjn,ha',hb'⟩ := innerProfileCell_integer_endpoints hn c ha hb hd
  have hj : 0 ≤ j := hi.trans hij.le
  have hiR : (i.toNat : ℝ) = (i : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hi
  have hjR : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hj
  refine ⟨i.toNat,j.toNat,?_,?_,?_,?_⟩
  · omega
  · omega
  · rw [hiR]
    exact ha'
  · rw [hjR]
    exact hb'

theorem innerProfileCell_block_endpoints {m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (c : ℝ × ℝ) (ha : 0 ≤ c.1) (hb : c.1+c.2 ≤ 1)
    (hd : 0 < (innerProfileCell m c).2) :
    ∃ i j : ℕ, j < i ∧ i ≤ m ∧
      (innerProfileCell m c).1 = (blockDepth (m*B) B i : ℝ)/(m*B : ℕ) ∧
      (innerProfileCell m c).1+(innerProfileCell m c).2 =
        (blockDepth (m*B) B j : ℝ)/(m*B : ℕ) := by
  obtain ⟨a,b,hab,hbm,ha',hb'⟩ := innerProfileCell_natural_endpoints hm c ha hb hd
  refine ⟨m-a,m-b,by omega,Nat.sub_le _ _,?_,?_⟩
  · rw [normalized_blockDepth hm hB (hab.le.trans hbm)]
    exact ha'
  · rw [normalized_blockDepth hm hB hbm]
    exact hb'

end Falconer.Regularization

end OAI
