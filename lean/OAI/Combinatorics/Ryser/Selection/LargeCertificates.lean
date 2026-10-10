import OAI.Combinatorics.Ryser.Selection.FeasibleDensity
import OAI.Combinatorics.Ryser.Selection.PoolCounts
import OAI.Combinatorics.Ryser.Selection.UnusedProduct

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem sum_fresh_feasibleDensity_ge (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hdensity : δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2 ≤
      (feasibleMass data I T pool : ℝ)) :
    ((K : ℝ) * δ - 2) * I.card ≤
      ∑ e ∈ freshTargets I T, feasibleDensity data T pool e.val.1 := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmass : δ * (I.card : ℝ) ≤ ∑ i ∈ I, feasibleDensity data T pool i := by
    rw [sum_feasibleDensity]
    exact (le_div_iff₀ (pow_pos hq 2)).mpr hdensity
  have hcount : (∑ i ∈ I, (exposedCount T i : ℝ)) ≤ 2 * (I.card : ℝ) := by
    have hnat : (∑ i ∈ I, exposedCount T i) ≤ 2 * I.card := by
      rw [sum_exposedCount hT]
      exact hcard
    exact_mod_cast hnat
  rw [sum_freshTargets]
  exact unused_weight_ge I (feasibleDensity data T pool) (exposedCount T) K δ I.card
    (fun i _ => feasibleDensity_le_one data T pool i)
    (fun i _ => exposedCount_le T i) hmass hcount

theorem prob_noFeasibleOutside_join_le_of_density (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hdensity : δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2 ≤
      (feasibleMass data I T (frozenPool T x) : ℝ)) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) ≤
        Real.exp (-(((K : ℝ) * δ - 2) * I.card)) := by
  have hsum := sum_fresh_feasibleDensity_ge data I T (frozenPool T x) δ
    hT hcard hdensity
  refine (prob_noFeasibleOutside_join_le_exp_neg_sum data I T x).trans ?_
  exact Real.exp_le_exp.mpr (neg_le_neg hsum)

theorem prob_noFeasibleOutside_le_density_bad_add_exp (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K)) (δ : ℝ)
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      (poolLaw F n K).prob (fun pool =>
        (feasibleMass data I T pool : ℝ) <
          δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2) +
        Real.exp (-(((K : ℝ) * δ - 2) * I.card)) := by
  have hsplit := poolLaw_prob_split_le_bad T (NoFeasibleOutside data I T)
    (fun x => (feasibleMass data I T (frozenPool T x) : ℝ) <
      δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)
    (Real.exp (-(((K : ℝ) * δ - 2) * I.card))) (Real.exp_pos _).le
    (fun x hx => prob_noFeasibleOutside_join_le_of_density data I T x δ hT hcard
      (le_of_not_gt hx))
  rw [← prob_feasibleMass_lt_eq_exposed data I T
    (δ * (I.card : ℝ) * (Fintype.card F : ℝ) ^ 2)] at hsplit
  exact hsplit

end RyserCoveringCounterexample.Selection

end

end OAI
