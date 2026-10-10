import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionKernel
import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionPMF
import OAI.Combinatorics.BalancedRyser.Probability.UniformThreshold

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.SelectedDeletion

universe u

theorem initialGood_uniform_lower (h : CandidateGraphResult.{u}) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F →
        Real.exp (-1) / 2 ≤ offsetEventProbability
          {M : MergedPairs F | InitialGood M c C} := by
  obtain ⟨c, C, hc, hC, hthreshold⟩ := candidate_graph_uniform_threshold h
  obtain ⟨N, hN⟩ := hthreshold (Real.exp (-1) / 2) (by positivity)
  refine ⟨c, C, hc, hC, N, ?_⟩
  intro F hF hFin hDec hcard
  have hnear := (hN F hcard).2
  have hlower := (abs_lt.mp hnear).1
  change Real.exp (-1) / 2 ≤ offsetEventProbability
    {M : MergedPairs F | CandidateGraphGood M c C ∧ DistinctConstituents M}
  linarith

theorem result_of_uniform_fixedLaws
    (hcandidate : CandidateGraphResult.{u})
    (hfixed : ∀ c C : ℝ, 0 < c → 0 < C →
      ∃ K ρ : ℝ, ∃ ε : ℕ → ℝ, ∃ N : ℕ,
        0 < K ∧ 0 < ρ ∧ (∀ q, 0 ≤ ε q) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
          N ≤ Fintype.card F → ∀ M : MergedPairs F,
            InitialGood M c C → Nonempty (FixedLaw M K ρ (ε (Fintype.card F)))) :
    SelectedDeletionResult.{u} := by
  classical
  obtain ⟨c, C, hc, hC, NGood, hgood⟩ := initialGood_uniform_lower hcandidate
  obtain ⟨K, ρ, ε, NSel, hK, hρ, hε, hlim, hlaws⟩ := hfixed c C hc hC
  have hevent : ∀ᶠ q in atTop, ε q < (1 / 2 : ℝ) :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨NErr, hErr⟩ := eventually_atTop.1 hevent
  let K' : ℝ := max 1 K
  let ρ' : ℝ := min ρ (1 / 2)
  let a₀ : ℝ := Real.exp (-1) / 4
  let N : ℕ := max 4 (max NGood (max NSel NErr))
  have hK' : 1 ≤ K' := le_max_left _ _
  have hK'nonneg : 0 ≤ K' := le_trans (by norm_num) hK'
  have hρ'pos : 0 < ρ' := lt_min hρ (by norm_num)
  have hρ'one : ρ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hC₀ : 0 < a₀⁻¹ + 4 * K' :=
    add_pos_of_pos_of_nonneg (inv_pos.mpr ha₀) (mul_nonneg (by norm_num) hK'nonneg)
  refine ⟨c, C, K', ρ', a₀, a₀⁻¹ + 4 * K', ε, N,
    hc, hC, hK', hρ'pos, hρ'one, ha₀, hC₀, le_max_left _ _, hε, hlim, ?_⟩
  intro F _ _ _ hlarge
  have h4 : 4 ≤ Fintype.card F := (le_max_left _ _).trans hlarge
  have hlargeGood : NGood ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  have hlargeSel : NSel ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  have hlargeErr : NErr ≤ Fintype.card F := by dsimp [N] at hlarge; omega
  let laws : ∀ M : MergedPairs F, InitialGood M c C →
      FixedLaw M K' ρ' (ε (Fintype.card F)) := fun M hM =>
    (Classical.choice (hlaws F hlargeSel M hM)).relax hK.le (le_max_right _ _)
      (min_le_left _ _)
  have hsuccess : a₀ ≤ successMass (glue laws) := by
    have h := glue_successMass_lower_half laws
      (show 0 ≤ Real.exp (-1) / 2 by positivity)
      (hgood F hlargeGood) (hErr _ hlargeErr).le
    dsimp [a₀]
    linarith
  refine ⟨glue laws, glue_isExperiment laws, glue_fixedSuccessMass laws,
    glue_fixedCylinderMass_le laws hK'nonneg, hsuccess,
    glue_occupancyFailureMass_le laws (hε _), ?_⟩
  exact exists_realizing_dominated_law (glue_isExperiment laws) (by omega)
    hK'nonneg ha₀ (glue_fixedCylinderMass_le laws hK'nonneg) hsuccess

end Balanced.SelectedDeletion

end

end OAI
