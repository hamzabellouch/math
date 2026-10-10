import OAI.NumberTheory.JointDickman.Probability.ChannelGrid
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Grouping the manuscript grid into equal coarse cells -/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def channelBlockCount (m B : ℕ) : ℕ :=
  ⌈((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m⌉₊

theorem channelFineCount_eq (m B : ℕ) : channelFineCount m B = m * channelBlockCount m B := rfl

noncomputable def groupedLower (m k : ℕ) (a : Fin m × Fin k) : ℝ :=
  channelLower (m * k) (finProdFinEquiv a)

noncomputable def groupedUpper (m k : ℕ) (a : Fin m × Fin k) : ℝ :=
  channelUpper (m * k) (finProdFinEquiv a)

theorem grouped_width (m k : ℕ) (a : Fin m × Fin k) :
    groupedUpper m k a - groupedLower m k a = channelMesh (m * k) := channel_width _ _

theorem groupedLower_ge (m k : ℕ) (a : Fin m × Fin k) :
    1 / 2 ≤ groupedLower m k a := channelLower_ge _ _

theorem groupedUpper_le {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (a : Fin m × Fin k) :
    groupedUpper m k a ≤ 3 := channelUpper_le (Nat.mul_pos hm hk) _

theorem groupedCells_disjoint {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (a b : Fin m × Fin k) (s : ℝ)
    (ha : s ∈ Set.Ioc (groupedLower m k a) (groupedUpper m k a))
    (hb : s ∈ Set.Ioc (groupedLower m k b) (groupedUpper m k b)) : a = b :=
  finProdFinEquiv.injective (channelCells_disjoint (Nat.mul_pos hm hk) _ _ s ha hb)

theorem groupedLower_diameter {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (d : Fin m) (i j : Fin k) :
    |groupedLower m k (d, i) - groupedLower m k (d, j)| ≤ channelMesh m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hi : (i.val : ℝ) ≤ k := by exact_mod_cast i.isLt.le
  have hj : (j.val : ℝ) ≤ k := by exact_mod_cast j.isLt.le
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have heq : groupedLower m k (d, i) - groupedLower m k (d, j) =
      ((i.val : ℝ) - j.val) * channelMesh (m * k) := by
    change (1 / 2 + ((i.val + k * d.val : ℕ) : ℝ) * channelMesh (m * k)) -
      (1 / 2 + ((j.val + k * d.val : ℕ) : ℝ) * channelMesh (m * k)) = _
    push_cast
    ring
  have hmul : (k : ℝ) * channelMesh (m * k) = channelMesh m := by
    unfold channelMesh
    rw [Nat.cast_mul]
    field_simp
  rw [heq, abs_mul, abs_of_pos (channelMesh_pos (Nat.mul_pos hm hk))]
  calc
    _ ≤ (k : ℝ) * channelMesh (m * k) := by
      apply mul_le_mul_of_nonneg_right _ (channelMesh_pos (Nat.mul_pos hm hk)).le
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = _ := hmul

theorem grouped_total_mass {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (∑ _a : Fin m × Fin k, channelMesh (m * k)) = 5 / 2 := by
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]
  unfold channelMesh
  field_simp

theorem channelFineCount_lower {m B : ℕ} (hm : 0 < m) :
    (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) ≤ channelFineCount m B := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_left
    (Nat.le_ceil (((5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ)) / m)) hm0.le
  simpa only [channelFineCount, Nat.cast_mul, mul_div_cancel₀ _ hm0.ne'] using h

theorem channelMesh_fine_upper {m B : ℕ} (hm : 0 < m) (hB : 1 ≤ B) :
    channelMesh (channelFineCount m B) ≤ (5 / 2 : ℝ) / B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hr : (B : ℝ) ≤ (B : ℝ) ^ (11 / 10 : ℝ) := by
    conv_lhs => rw [← Real.rpow_one (B : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
  have hn : (B : ℝ) ≤ channelFineCount m B := by
    calc
      _ ≤ (5 / 2 : ℝ) * (B : ℝ) ^ (11 / 10 : ℝ) := by nlinarith
      _ ≤ _ := channelFineCount_lower hm
  unfold channelMesh
  exact div_le_div_of_nonneg_left (by norm_num) hB0 hn

end JointDickman

end OAI
