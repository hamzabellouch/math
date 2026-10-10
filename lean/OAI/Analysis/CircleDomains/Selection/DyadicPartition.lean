import OAI.Analysis.CircleDomains.Selection.DyadicTimes
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Dyadic partitions exhaust every compact interval inside an open set. -/

open Set Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def dyadicNode (n i : ℕ) : PathTime :=
  dyadicTime n ⟨min i (2 ^ n), Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem monotone_dyadicNode (n : ℕ) : Monotone (dyadicNode n) := by
  intro i j hij
  exact dyadicReal_mono n (min_le_min_right _ hij)

theorem dyadicNode_zero (n : ℕ) : dyadicNode n 0 = ⊥ := by
  apply Subtype.ext
  simp [dyadicNode, dyadicTime, dyadicReal]

theorem dyadicNode_last (n : ℕ) : dyadicNode n (2 ^ n) = ⊤ := by
  apply Subtype.ext
  simp [dyadicNode, dyadicTime, dyadicReal]

theorem dyadicNode_left (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicNode n i = dyadicLeft n i := by
  apply Subtype.ext
  simp [dyadicNode, dyadicLeft, dyadicTime]

theorem dyadicNode_right (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicNode n (i.val + 1) = dyadicRight n i := by
  apply Subtype.ext
  simp [dyadicNode, dyadicRight, dyadicTime]

theorem sum_dyadic_variations {Y : Type*} [PseudoEMetricSpace Y]
    (ρ : PathTime → Y) (n : ℕ) :
    ∑ i : Fin (2 ^ n), eVariationOn ρ (Icc (dyadicLeft n i) (dyadicRight n i)) =
      eVariationOn ρ univ := by
  have h := eVariationOn.sum' ρ (monotone_dyadicNode n) (n := 2 ^ n)
  rw [dyadicNode_zero, dyadicNode_last, Icc_bot_top] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [dyadicNode_left, dyadicNode_right]

theorem dyadicCell_dist_le (n : ℕ) (i : Fin (2 ^ n))
    {s t : PathTime} (hs : s ∈ Icc (dyadicLeft n i) (dyadicRight n i))
    (ht : t ∈ Icc (dyadicLeft n i) (dyadicRight n i)) :
    dist s t ≤ 1 / (2 : ℝ) ^ n := by
  change |(s : ℝ) - (t : ℝ)| ≤ _
  have hlen : (dyadicRight n i : ℝ) - (dyadicLeft n i : ℝ) = 1 / (2 : ℝ) ^ n := by
    change ((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n - (i.val : ℝ) / (2 : ℝ) ^ n = _
    push_cast
    ring
  change (dyadicLeft n i : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ (dyadicRight n i : ℝ) at hs
  change (dyadicLeft n i : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (dyadicRight n i : ℝ) at ht
  rw [abs_le]
  constructor <;> linarith

theorem exists_dyadic_cells_inside {V : Set PathTime} (hV : IsOpen V)
    {a b : PathTime} (hab : Icc a b ⊆ V) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hV hab
  have hlim : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hh := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hp
    convert hh using 1
    funext n
    simp only [Function.comp_apply, one_div]
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨n, fun i hi t ht => hsub ?_⟩
  obtain ⟨s, hs, hsi⟩ := hi
  exact Metric.mem_thickening_iff.mpr ⟨s, hsi, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩

end CircleDomainRigidity

end

end OAI
