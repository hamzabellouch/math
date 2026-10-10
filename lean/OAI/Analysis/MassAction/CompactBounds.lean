import Mathlib

namespace OAI

universe uIota

noncomputable section

namespace Problem326

/-- A compact set in a finite-dimensional positive orthant lies in a uniform
positive box. Neither nonemptiness nor positive dimension is necessary. -/
theorem compact_positive_uniform_bounds {ι : Type uIota} [Finite ι]
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, ∀ i, 0 < x i) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ x ∈ K, ∀ i, ε ≤ x i ∧ x i ≤ ε⁻¹ := by
  let S : Set ℝ := ⋃ i : ι, (fun x : ι → ℝ => x i) '' K
  have hS : IsCompact S :=
    isCompact_iUnion (fun i => hK.image (continuous_apply i))
  have hSpos : ∀ y ∈ S, 0 < y := by
    intro y hy
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hy
    exact hpos x hx i
  obtain ⟨a, ha, haS⟩ := hS.exists_forall_le' continuous_id.continuousOn hSpos
  have hinv : ContinuousOn (fun y : ℝ => y⁻¹) S :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (hSpos y hy))
  obtain ⟨b, hb, hbS⟩ := hS.exists_forall_le' hinv
    (fun y hy => inv_pos.mpr (hSpos y hy))
  let ε : ℝ := min (1 / 2) (min a b)
  have hε : 0 < ε := lt_min (by norm_num) (lt_min ha hb)
  refine ⟨ε, hε, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  intro x hx i
  have hmem : x i ∈ S := Set.mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  have hεa : ε ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨hεa.trans (haS _ hmem), ?_⟩
  have hle : ε ≤ (x i)⁻¹ := hεb.trans (hbS _ hmem)
  exact (le_inv_comm₀ hε (hpos x hx i)).mp hle

end Problem326

end

end OAI
