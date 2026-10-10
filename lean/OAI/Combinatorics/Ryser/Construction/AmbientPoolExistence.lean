import OAI.Combinatorics.Ryser.Construction.AmbientDeletionPoolLaw
import OAI.Combinatorics.Ryser.Construction.GroupSelection
import OAI.Combinatorics.Ryser.Construction.PoolThinAsymptotic
import OAI.Combinatorics.Ryser.LineCover.Main
import OAI.Combinatorics.Ryser.Selection.Main

namespace OAI

noncomputable section
open scoped Classical

namespace RyserCoveringCounterexample.Construction

universe uk uf

variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]

def GoodAmbientPool {F : Type uf} [Field F] [Fintype F] [DecidableEq F]
    (σ : k →+* F) (u v : k) (huv : u ≠ v)
    (a : GadgetOutcome k) (ha : OriginalLineDensity a) (K : ℕ)
    (pool : AmbientPool σ K) : Prop :=
  Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool) ∧
    LineCover.GoodLineCover (ambientDeletionDelta (Fintype.card k) K)
      (ambientDeletionDelta (Fintype.card k) K / 10)
      (ambientPoolConfig σ u v huv a ha K pool) ∧
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv) pool

theorem exists_goodAmbientPool_uniform
    (u v : k) (huv : u ≠ v) (a : GadgetOutcome k) (ha : OriginalLineDensity a)
    (hs : 2 ≤ Fintype.card k) :
    ∃ K Q : ℕ, 6 ≤ K ∧
      ∀ (F : Type uf) [Field F] [Fintype F] [DecidableEq F] (σ : k →+* F),
        Q ≤ Fintype.card F → Incidence.SmallProperSubfields F →
        (1 + ambientDeletionDelta (Fintype.card k) K / 10 * Fintype.card F <
          ambientDeletionDelta (Fintype.card k) K * Fintype.card F / 2) ∧
        ∃ pool : AmbientPool σ K, GoodAmbientPool σ u v huv a ha K pool := by
  classical
  let s := Fintype.card k
  let D := groupSelectionConstant s
  have hD : 1 ≤ D := by dsimp [D, groupSelectionConstant]; omega
  obtain ⟨K, hK, hselection⟩ := Selection.compatible_selection_uniform.{uf} D hD
  obtain ⟨QS, hQS⟩ := hselection (1 / 4) (by norm_num)
  let δ := ambientDeletionDelta s K
  let ρ := δ / 10
  let DA := ambientDeletionConstant s K
  have hδ : 0 < δ := ambientDeletionDelta_pos s K
  have hρ : 0 < ρ := div_pos hδ (by norm_num)
  have hDA : 0 < DA := lt_of_lt_of_le (by decide : 0 < 2)
    (ambientDeletionConstant_two_le s K)
  obtain ⟨QL, hQL⟩ := LineCover.uniform_linecover_probability.{uf}
    DA δ ρ hDA hδ hρ (1 / 4) (by norm_num)
  obtain ⟨QT, hQT⟩ := exists_thinFailure_cutoff s K (η := 1 / 4) (by norm_num)
  let QF : ℕ := ⌈10 / δ⌉₊ + 1
  refine ⟨K, QS + QL + QT + 2 * (s - 1) ^ 2 + QF, hK, ?_⟩
  intro F instField instFintype instDecidable σ hq hsub
  have hqS : QS ≤ Fintype.card F := by omega
  have hqL : QL ≤ Fintype.card F := by omega
  have hqT : QT ≤ Fintype.card F := by omega
  have hsmall : 2 * (Fintype.card k - 1) ^ 2 ≤ Fintype.card F := by
    change 2 * (s - 1) ^ 2 ≤ Fintype.card F
    omega
  have hqF : QF ≤ Fintype.card F := by omega
  have hqFreal : (QF : ℝ) ≤ Fintype.card F := by exact_mod_cast hqF
  have hforce : 1 + ρ * Fintype.card F < δ * Fintype.card F / 2 := by
    have hceil : 10 / δ ≤ (⌈10 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have hlarge : 10 / δ < (Fintype.card F : ℝ) := by
      dsimp [QF] at hqFreal
      push_cast at hqFreal
      linarith
    have hproduct : 10 < (Fintype.card F : ℝ) * δ := (div_lt_iff₀ hδ).mp hlarge
    dsimp [ρ]
    nlinarith
  refine ⟨hforce, ?_⟩
  let μ := poolThinLaw (F := F) (ConfigurationGroup σ) K
  let Selected : AmbientPool σ K → Prop := fun pool =>
    Selection.HasCompatibleChoice (groupSelectionData σ u v huv)
      (ambientFlatPoolEquiv σ K pool)
  let Rigid : AmbientPool σ K → Prop := fun pool =>
    LineCover.GoodLineCover δ ρ (ambientPoolConfig σ u v huv a ha K pool)
  let Thin : AmbientPool σ K → Prop :=
    PoolThin (groupPoints σ u v huv) (groupAltered σ u v huv)
  have hselect : 1 - (1 / 4 : ℝ) ≤ μ.prob Selected := by
    have h := hQS F (Fintype.card (ConfigurationGroup σ)) (groupSelectionData σ u v huv)
      (groupSelectionData_bounded σ u v huv hs) hqS
    rw [← poolThinLaw_map_ambientFlatPoolEquiv σ K, FiniteLaw.prob_map] at h
    exact h
  have hrigid : 1 - (1 / 4 : ℝ) ≤ μ.prob Rigid := by
    have h := hQL F hqL hsub (ambientDeletionProcess σ u v huv a ha K hs hsmall)
    change 1 - (1 / 4 : ℝ) ≤ (FiniteLaw.pi (ambientTrials σ u v huv a ha K)).prob
      (LineCover.GoodLineCover δ ρ) at h
    rw [← poolThinLaw_map_ambientPoolConfig σ u v huv a ha K, FiniteLaw.prob_map] at h
    exact h
  have hthin : 1 - (1 / 4 : ℝ) ≤ μ.prob Thin := by
    have h := prob_groupPoolThin_ge σ u v huv K
    have htail := hQT (Fintype.card F) hqT
    exact (sub_le_sub_left htail 1).trans h
  have hex : ∃ pool : AmbientPool σ K, Selected pool ∧ Rigid pool ∧ Thin pool := by
    by_contra hnot
    have himp : ∀ pool, Selected pool → ¬ Rigid pool ∨ ¬ Thin pool := by
      intro pool hselected
      by_cases hr : Rigid pool
      · exact Or.inr (fun ht => hnot ⟨pool, hselected, hr, ht⟩)
      · exact Or.inl hr
    have hmono := (μ.prob_mono himp).trans (μ.prob_union_le (fun pool => ¬ Rigid pool)
      (fun pool => ¬ Thin pool))
    rw [μ.prob_compl, μ.prob_compl] at hmono
    linarith
  obtain ⟨pool, hselected, hrigid', hthin'⟩ := hex
  exact ⟨pool, hselected, hrigid', hthin'⟩

end RyserCoveringCounterexample.Construction

end

end OAI
