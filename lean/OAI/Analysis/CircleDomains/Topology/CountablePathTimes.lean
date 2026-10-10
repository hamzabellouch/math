import OAI.Analysis.CircleDomains.Topology.AffinePathTime
import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Decreasing dyadic intervals for the countable collar concatenation. -/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

def collarTime (n : ℕ) : PathTime :=
  ⟨(1 / 2 : ℝ) ^ n, pow_nonneg (by norm_num) n, pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem collarTime_pos (n : ℕ) : (⊥ : PathTime) < collarTime n := by
  change (0 : ℝ) < (1 / 2 : ℝ) ^ n
  positivity

theorem collarTime_zero : collarTime 0 = ⊤ := by
  apply Subtype.ext
  simp [collarTime]

theorem collarTime_strictAnti : StrictAnti collarTime := by
  apply strictAnti_nat_of_succ_lt
  intro n
  change (1 / 2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) ^ n
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

theorem collarTime_tendsto : Tendsto collarTime atTop (𝓝 (⊥ : PathTime)) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

theorem exists_collarTime_cell {t : PathTime} (ht : ⊥ < t) :
    ∃ n, collarTime (n + 1) < t ∧ t ≤ collarTime n := by
  obtain ⟨n, hn⟩ := exists_nat_pow_near_of_lt_one
    (show (0 : ℝ) < t from ht) t.property.2
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨n, hn⟩

def collarCell (n : ℕ) : Set PathTime := Icc (collarTime (n + 1)) (collarTime n)

theorem collarCell_disjoint_interiors :
    Pairwise (Disjoint on (fun n => Ioo (collarTime (n + 1)) (collarTime n))) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hb := collarTime_strictAnti.antitone (Nat.succ_le_of_lt h)
    exact (hi.1.trans hj.2).not_ge hb
  · have hb := collarTime_strictAnti.antitone (Nat.succ_le_of_lt h)
    exact (hj.1.trans hi.2).not_ge hb

theorem collarCell_complement_countable :
    (⋃ n, Ioo (collarTime (n + 1)) (collarTime n))ᶜ.Countable := by
  apply (Set.countable_range collarTime |>.insert ⊥).mono
  intro t ht
  by_cases hzero : t = ⊥
  · exact Or.inl hzero
  · obtain ⟨n, hlow, hhigh⟩ := exists_collarTime_cell (bot_lt_iff_ne_bot.mpr hzero)
    have heq : t = collarTime n := by
      by_contra hne
      have hint : t ∈ Ioo (collarTime (n + 1)) (collarTime n) :=
        ⟨hlow, hhigh.lt_of_ne hne⟩
      exact ht (mem_iUnion.mpr ⟨n, hint⟩)
    exact Or.inr ⟨n, heq.symm⟩

abbrev PositivePathTime := {t : PathTime // ⊥ < t}

theorem collarCells_locallyFinite :
    LocallyFinite (fun n => (Subtype.val : PositivePathTime → PathTime) ⁻¹' collarCell n) := by
  intro t
  have hevent : ∀ᶠ n in atTop, collarTime n < t.val :=
    collarTime_tendsto.eventually (gt_mem_nhds t.property)
  obtain ⟨N, hN⟩ := hevent.exists
  refine ⟨{s | collarTime N < (s : PathTime)}, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_subtype_val).mem_nhds hN
  · apply (Set.finite_lt_nat N).subset
    rintro n ⟨s, hs, hsn⟩
    change collarTime N < s.val at hsn
    by_contra hn
    have hle := collarTime_strictAnti.antitone (Nat.le_of_not_gt hn)
    exact (hsn.trans_le hs.2).not_ge hle

theorem collarCells_cover_positive :
    (⋃ n, (Subtype.val : PositivePathTime → PathTime) ⁻¹' collarCell n) = univ := by
  apply eq_univ_of_forall
  intro t
  obtain ⟨n, hlow, hhigh⟩ := exists_collarTime_cell t.property
  exact mem_iUnion.mpr ⟨n, hlow.le, hhigh⟩

end CircleDomainRigidity

end

end OAI
