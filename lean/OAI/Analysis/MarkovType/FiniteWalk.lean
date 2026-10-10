import OAI.Analysis.MarkovType.FiniteWalkWitness
import OAI.Analysis.MarkovType.WalkMarkedDisplacement
import OAI.Analysis.MarkovType.ChartPathProbability
import Mathlib.Tactic.FieldSimp

namespace OAI

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace MarkovSuperreflexivity

open FiniteWalkDrift

def normalizedChartEdgeLabel (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) : C00 :=
  (N.alternatingNorm (walkWindowLength n))⁻¹ • rawChartEdgeLabel ν e

theorem normalizedChartEdgeLabel_odd (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) :
    OddLabel (concreteChartChain ν) (normalizedChartEdgeLabel N ν) := by
  intro e
  change (N.alternatingNorm (walkWindowLength n))⁻¹ •
      rawWalkLabel e.2.2.val e.2.1.inv e.1.val =
    -((N.alternatingNorm (walkWindowLength n))⁻¹ •
      rawWalkLabel e.1.val e.2.1 e.2.2.val)
  rw [rawWalkLabel_odd, smul_neg]

theorem normalizedChartEdgeLabel_unit (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) :
    N (normalizedChartEdgeLabel N ν e) = 1 := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  rw [normalizedChartEdgeLabel, N.smul, abs_of_pos (inv_pos.mpr hD)]
  change (N.alternatingNorm (walkWindowLength n))⁻¹ *
      N (rawWalkLabel e.1.val e.2.1 e.2.2.val) = 1
  rw [rawWalkLabel_norm, inv_mul_cancel₀ (ne_of_gt hD)]

theorem normalizedChartEdgeLabel_supportedBelow (N : OrderedNorm) {n B : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B)) (e : ConcreteChartEdge ν) :
    C00.SupportedBelow (normalizedChartEdgeLabel N ν e) B := by
  intro k hk
  change (N.alternatingNorm (walkWindowLength n))⁻¹ *
      rawWalkLabel e.1.val e.2.1 e.2.2.val k = 0
  rw [rawWalkLabel_supportedBelow e.1.val e.2.2.val e.2.1 k hk, mul_zero]

theorem normalizedChartEdgeSum_norm (N : OrderedNorm) {n B t : ℕ}
    (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) t) :
    N (edgeSum (normalizedChartEdgeLabel N ν) ω) =
      (N.alternatingNorm (walkWindowLength n))⁻¹ *
        N (edgeSum (rawChartEdgeLabel ν) ω) := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  simp only [edgeSum, normalizedChartEdgeLabel, ← Finset.smul_sum, N.smul,
    abs_of_pos (inv_pos.mpr hD)]

theorem normalizedChartEdgeSum_displacement (N : OrderedNorm) {n B : ℕ}
    (hn : 0 < n) (ν : FiniteLaw (Chart (walkLandmarks n) B))
    (ω : MarkedPath (ConcreteChartState ν) (ConcreteChartEdge ν) n)
    (hvalid : markedValid (concreteChartChain ν) ω)
    (hell : (n : ℝ) / 4 ≤
      (reducedLength (List.ofFn (concreteChartPathLetters ω)) : ℝ))
    (hgood : ∀ i : Fin n, concreteChartGood (ω.2 i)) :
    (n : ℝ) / 24 ≤ N (edgeSum (normalizedChartEdgeLabel N ν) ω) := by
  have hD := N.alternatingNorm_pos (walkWindowLength_pos n)
  have hraw := rawChartEdgeSum_displacement N hn ν ω hvalid hell hgood
  rw [normalizedChartEdgeSum_norm]
  have hdiv : (n : ℝ) / 24 ≤
      N (edgeSum (rawChartEdgeLabel ν) ω) / N.alternatingNorm (walkWindowLength n) := by
    apply (le_div_iff₀ hD).mpr
    nlinarith
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

theorem finiteWalk (N : OrderedNorm) (n : ℕ) (hn : 0 < n) :
    Nonempty (FiniteWalkWitness N n) := by
  classical
  obtain ⟨B, ν, hprob⟩ :=
    exists_concreteChartPath_valid_tail_all_good (walkLandmarks n) n hn
  have hescape : (3 : ℝ) / 20 ≤
      markedProb (concreteChartChain ν) n
        (fun ω => (n : ℝ) / 24 ≤ N (edgeSum (normalizedChartEdgeLabel N ν) ω)) := by
    apply le_trans hprob
    apply eventMass_mono (markedPathWeight (concreteChartChain ν) n)
      (markedPathWeight_nonneg (concreteChartChain ν) n)
    intro ω hω
    exact normalizedChartEdgeSum_displacement N hn ν ω hω.1 hω.2.1 hω.2.2
  exact ⟨{
    State := ConcreteChartState ν
    Edge := ConcreteChartEdge ν
    stateFintype := inferInstance
    edgeFintype := inferInstance
    chain := concreteChartChain ν
    coordinateBound := B
    label := normalizedChartEdgeLabel N ν
    odd := normalizedChartEdgeLabel_odd N ν
    support_bound := normalizedChartEdgeLabel_supportedBelow N ν
    unit := normalizedChartEdgeLabel_unit N ν
    escape := hescape
  }⟩

end MarkovSuperreflexivity

end

end OAI
