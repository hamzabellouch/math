import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.FinishSupportSubset
import OAI.Combinatorics.TriangleRemoval.Stability.GridCavityWeightLower
import OAI.Combinatorics.TriangleRemoval.Process.AveragedSingletonSurvivalError

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem goodPrefix_survival_moments (c C : ℝ) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ hne : G.Nonempty,
      (|pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e})-
        cavityReference (prefixD n) 1| ≤
          8192*(1+2*prefixD n)^48/prefixD n^50+ε*cavityReference (prefixD n) 1) ∧
      (|pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f}))-
          (cavityReference (prefixD n) 1)^2| ≤
        65536*(1+2*prefixD n)^48/prefixD n^50+8/(n : ℝ)+
          (2*ε+ε^2)*(cavityReference (prefixD n) 1)^2) := by
  filter_upwards [goodPrefix_cavity_stability hc hε,
    averaged_singleton_collisionCost c C hc,averaged_disjoint_collisionCost c C hc,
    goodPrefix_rootOverlap hc,goodPrefix_full_continuous_rows hc] with n hrel hsingle hpair hover hpos
  intro G hG hne
  have hr := (hrel C G hG 1 ⟨by norm_num,le_rfl⟩).1
  constructor
  · exact (averaged_singleton_survival_error G hne (prefixD n) ε hpos.1 hr).trans
      (add_le_add (hsingle G hG hne) le_rfl)
  · exact (averaged_pair_survival_error G hne hG.1 (prefixD n) ε hpos.1 hε.le hr).trans
      (add_le_add (add_le_add (hpair G hG hne) (hover C G hG hne)) le_rfl)

lemma focusSurvival_singleton_mean {n : ℕ} (G : Graph n) (e : Finset (Fin n)) :
    focusSurvival G {e} = pmfMean (finish G) (fun H => if e ∈ H then 1 else 0) := by
  classical
  unfold focusSurvival
  rw [trueProbability_map]
  simp only [Finset.singleton_subset_iff,decide_eq_true_eq,pmfMean]

lemma focusSurvival_pair_mean {n : ℕ} (G : Graph n) (e f : Finset (Fin n)) :
    focusSurvival G {e,f} = pmfMean (finish G) (fun H => if e ∈ H ∧ f ∈ H then 1 else 0) := by
  classical
  unfold focusSurvival
  rw [trueProbability_map]
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,decide_eq_true_eq,pmfMean]

theorem terminal_first_focus_moment {n : ℕ} (G : Graph n) (hne : G.Nonempty) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e => focusSurvival G {e}) =
      pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ) := by
  simp_rw [focusSurvival_singleton_mean]
  rw [pmfMean_swap]
  exact terminal_first_edge_moment G hne

theorem terminal_second_focus_moment {n : ℕ} (G : Graph n) (hne : G.Nonempty) :
    pmfMean (PMF.uniformOfFinset G hne) (fun e =>
      pmfMean (PMF.uniformOfFinset G hne) (fun f => focusSurvival G {e,f})) =
      pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2 := by
  simp_rw [focusSurvival_pair_mean]
  calc
    _ = pmfMean (PMF.uniformOfFinset G hne) (fun e =>
        pmfMean (finish G) (fun H =>
          pmfMean (PMF.uniformOfFinset G hne) (fun f =>
            if e ∈ H ∧ f ∈ H then 1 else 0))) := by
      apply congrArg
      funext e
      exact pmfMean_swap _ _ _
    _ = pmfMean (finish G) (fun H =>
        pmfMean (PMF.uniformOfFinset G hne) (fun e =>
          pmfMean (PMF.uniformOfFinset G hne) (fun f =>
            if e ∈ H ∧ f ∈ H then 1 else 0))) := pmfMean_swap _ _ _
    _ = _ := terminal_second_edge_moment G hne

end SharpTerminalLeave

end

end OAI
