import OAI.Analysis.CircleDomains.Selection.DyadicPartition
import OAI.Analysis.CircleDomains.Modulus.PathLengthLocality

namespace OAI

/-! Atomless measures split exactly over the closed dyadic cells. -/

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem restrict_Icc_add (μ : Measure PathTime) [NullSingletonClass μ]
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) :
    μ.restrict (Icc a c) = μ.restrict (Icc a b) + μ.restrict (Icc b c) := by
  have hd : AEDisjoint μ (Icc a b) (Icc b c) := by
    rw [AEDisjoint, Icc_inter_Icc_eq_singleton hab hbc]
    exact measure_singleton b
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  exact Measure.restrict_union₀ hd measurableSet_Icc.nullMeasurableSet

theorem sum_dyadic_restrict (μ : Measure PathTime) [NullSingletonClass μ] (n : ℕ) :
    ∑ i : Fin (2 ^ n), μ.restrict (Icc (dyadicLeft n i) (dyadicRight n i)) = μ := by
  induction n with
  | zero =>
    change (∑ i : Fin 1, μ.restrict (Icc (dyadicLeft 0 i) (dyadicRight 0 i))) = μ
    rw [Fin.sum_univ_one]
    have hl : dyadicLeft 0 0 = ⊥ := (dyadicNode_left 0 0).symm.trans (dyadicNode_zero 0)
    have hr : dyadicRight 0 0 = ⊤ := (dyadicNode_right 0 0).symm.trans (dyadicNode_last 0)
    rw [hl, hr, Icc_bot_top, Measure.restrict_univ]
  | succ n ih =>
    rw [sum_dyadic_children]
    convert ih using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← dyadicRight_even, ← restrict_Icc_add μ (dyadicLeft_le_right _ _)]
    · rw [dyadicLeft_even, dyadicRight_odd]
    · rw [dyadicRight_even]
      exact dyadicLeft_le_right _ _

theorem eventually_dyadic_cells_inside {V : Set PathTime} (hV : IsOpen V)
    {a b : PathTime} (hab : Icc a b ⊆ V) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      Icc (dyadicLeft n i) (dyadicRight n i) ⊆ V := by
  obtain ⟨δ, hδ, hsub⟩ := isCompact_Icc.exists_thickening_subset_open hV hab
  have hp : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hp using 1
    funext n
    simp only [Function.comp_apply, one_div]
  filter_upwards [(tendsto_order.1 hlim).2 δ hδ] with n hn i hi t ht
  obtain ⟨s, hs, hsi⟩ := hi
  exact hsub (Metric.mem_thickening_iff.mpr
    ⟨s, hsi, (dyadicCell_dist_le n i ht hs).trans_lt hn⟩)

end CircleDomainRigidity

end

end OAI
