import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.FiniteChargeSelection
import OAI.Analysis.RieszRectifiability.Nets.CapturedCellSeedMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem finite_parent_mass_of_seed_charges {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (F : Finset (SupportCellDescendant μ R hR k z))
    (seed : SupportCellDescendant μ R hR k z → SupportCellDescendant μ R hR k z)
    (Osc : SupportCellDescendant μ R hR k z → Prop) (I : ℕ) (M K : ℝ≥0∞)
    (hseed : ∀ i ∈ F, i.depth ≤ (seed i).depth ∧ (seed i).depth ≤ i.depth + I ∧
      (seed i).cell ⊆ i.cell)
    (hmass : ∀ i ∈ F, μ i.cell ≤ M * μ (seed i).cell)
    (hgap : ∀ i ∈ F, ∀ j ∈ F, (seed i).depth < j.depth → j.cell ⊆ (seed i).cell →
      ∃ t : {t // Osc t}, (seed i).depth ≤ t.val.depth ∧ t.val.depth < j.depth ∧ j.cell ⊆ t.val.cell)
    (hcarleson : ∑' t : {t // Osc t}, μ t.val.cell ≤ K * μ (cleanSupportCell μ R hR k z)) :
    ∑ i ∈ F, μ i.cell ≤ (M * ((I + 1 : ℕ) : ℝ≥0∞) * (1 + K)) *
      μ (cleanSupportCell μ R hR k z) := by
  classical
  obtain ⟨O, hO⟩ := exists_finite_pair_witnesses F
    (fun i j => (seed i).depth < j.depth ∧ j.cell ⊆ (seed i).cell)
    (fun i j (t : {t // Osc t}) =>
      (seed i).depth ≤ t.val.depth ∧ t.val.depth < j.depth ∧ j.cell ⊆ t.val.cell)
    (fun i hi j hj hrel => hgap i hi j hj hrel.1 hrel.2)
  let emb : {t // Osc t} ↪ SupportCellDescendant μ R hR k z := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound := captured_cell_seed_mass_bound μ R hR k z F (O.map emb) seed I hseed (by
    intro i hi j hj hdepth hsub
    obtain ⟨t, ht, hlow, hhigh, hcontain⟩ := hO i hi j hj ⟨hdepth, hsub⟩
    exact ⟨t.val, Finset.mem_map.mpr ⟨t, ht, rfl⟩, hlow, hhigh, hcontain⟩)
  have hOmass : ∑ t ∈ O.map emb, μ t.cell ≤ K * μ (cleanSupportCell μ R hR k z) := by
    rw [Finset.sum_map]
    exact (ENNReal.sum_le_tsum O).trans hcarleson
  calc
    _ ≤ ∑ i ∈ F, M * μ (seed i).cell := Finset.sum_le_sum hmass
    _ = M * ∑ i ∈ F, μ (seed i).cell := (Finset.mul_sum ..).symm
    _ ≤ M * (((I + 1 : ℕ) : ℝ≥0∞) *
        (μ (cleanSupportCell μ R hR k z) + ∑ t ∈ O.map emb, μ t.cell)) :=
      mul_le_mul_of_nonneg_left hbound (zero_le)
    _ ≤ M * (((I + 1 : ℕ) : ℝ≥0∞) *
        (μ (cleanSupportCell μ R hR k z) + K * μ (cleanSupportCell μ R hR k z))) := by
      gcongr
    _ = _ := by ring

end

end RieszRectifiability

end OAI
