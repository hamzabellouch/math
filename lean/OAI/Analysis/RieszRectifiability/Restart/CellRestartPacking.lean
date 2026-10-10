import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.FiniteSeedPacking

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def cellRestartsAfter {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (i : SupportCellDescendant μ R hR k z) : Prop :=
  i.depth = 0 ∨ ∃ q : SupportCellDescendant μ R hR k z,
    Bad q ∧ i.depth = q.depth + 1 ∧ i.cell ⊆ q.cell

theorem finite_restart_roots_mass_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop) (K : ℝ≥0∞)
    (hpack : ∑' q : {q // Bad q}, μ q.val.cell ≤ K * μ (cleanSupportCell μ R hR k z))
    (F : Finset (SupportCellDescendant μ R hR k z))
    (hF : ∀ i ∈ F, cellRestartsAfter Bad i) :
    ∑ i ∈ F, μ i.cell ≤ (1 + K) * μ (cleanSupportCell μ R hR k z) := by
  have h := finite_parent_mass_of_seed_charges μ R hR k z F id Bad 0 1 K
    (fun i _ => ⟨le_rfl, by simp, Subset.rfl⟩)
    (fun i _ => by simp)
    (by
      intro i _ j hj hdepth _
      change i.depth < j.depth at hdepth
      rcases hF j hj with hzero | ⟨q, hbad, hqdepth, hsub⟩
      · omega
      · refine ⟨⟨q, hbad⟩, ?_, ?_, hsub⟩
        · change i.depth ≤ q.depth
          omega
        · change q.depth < j.depth
          omega)
    hpack
  simpa only [Nat.zero_add, Nat.cast_one, one_mul] using! h

theorem restart_roots_total_mass_le {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Bad : SupportCellDescendant μ R hR k z → Prop) (K : ℝ≥0∞)
    (hpack : ∑' q : {q // Bad q}, μ q.val.cell ≤ K * μ (cleanSupportCell μ R hR k z)) :
    ∑' i : {i // cellRestartsAfter Bad i}, μ i.val.cell ≤
      (1 + K) * μ (cleanSupportCell μ R hR k z) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  let e : {i // cellRestartsAfter Bad i} ↪ SupportCellDescendant μ R hR k z :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hF : ∀ i ∈ F.map e, cellRestartsAfter Bad i := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  have h := finite_restart_roots_mass_le μ R hR k z Bad K hpack (F.map e) hF
  simpa only [Finset.sum_map] using! h

end

end RieszRectifiability

end OAI
