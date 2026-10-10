import OAI.Algebra.DepthFive.LowerSchedule
import OAI.Algebra.DepthFive.ScheduleWeightBridge
import OAI.Algebra.DepthFive.WordSum

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.LowerParameters

/-- The full graph-word estimate for the actual balanced layer partition.
All path-graph, endpoint, flip, and cardinality premises are discharged. -/
lemma balanced_word_sum_bound_of_product {n : ℕ} (hn : 4 ≤ n + 1)
    (A B E : ℝ) (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hB : 0 ≤ B) (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ ((Finset.univ.filter (fun i => balancedLayer hn i = true)).filter
        (fun i => w i = true)).card *
      B ^ ((Finset.univ \ Finset.univ.filter (fun i => balancedLayer hn i = true)).filter
        (fun i => w i = true)).card ≤
      Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w : Fin (n + 1) → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges (n + 1))
        (Finset.univ.filter (fun i => balancedLayer hn i = true))
        BalancedSchedule.adjacent A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let V := Finset.univ.filter (fun i => balancedLayer hn i = true)
  let first : Fin (n + 1) := ⟨0, by omega⟩
  let S := V.erase first
  have hfirst : first ∈ V := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, balancedLayer_first hn⟩
  apply WordSum.sum_actual_weight_le_exp_of_endpoints n A B E
    (BalancedSchedule.internalEdges (n + 1)) V S BalancedSchedule.adjacent
  · exact Finset.erase_subset _ _
  · intro i hi j hij hj
    exact balancedLayer_independent hn (Finset.mem_filter.mp hi).2
      (Finset.mem_filter.mp hj).2 hij
  · intro e he
    exact BalancedSchedule.internalEdges_adjacent he
  · intro i hi
    obtain ⟨hifirst, hiV⟩ := Finset.mem_erase.mp hi
    have hival : i.val ≠ 0 := by
      intro h
      exact hifirst (Fin.ext h)
    have hlast : i.val + 1 < n + 1 := by
      by_contra hf
      have heq : i = ⟨(n + 1) - 1, by omega⟩ := by
        apply Fin.ext
        change i.val = (n + 1) - 1
        have := i.isLt
        omega
      have hitrue := (Finset.mem_filter.mp hiV).2
      rw [heq, balancedLayer_final hn] at hitrue
      cases hitrue
    rw [BalancedSchedule.endpointDegree_internalEdges]
    exact BalancedSchedule.card_internalEnds_eq_two i (by omega) hlast
  · intro w
    rw [BalancedSchedule.internalEdges_eq_pathEdges,
      SwitchRestoration.switchCount_pathEdges]
    simp [WordSwitches.switches, Finset.card_filter]
  · change (V \ V.erase first).card ≤ 1
    rw [Finset.sdiff_erase hfirst]
    simp
  · have hcard : V.card = k (n + 1) := balancedLayer_card_true hn
    rw [hcard]
    have hle : 2 * k (n + 1) ≤ n + 1 := by
      have h := two_mul_k_add_s (n + 1)
      omega
    exact_mod_cast hle
  · exact hA
  · exact hAN
  · exact hB
  · exact hE
  · exact hprod

/-- The canonical balanced schedule satisfies the complete corrected-word bound.
The only premises are the scalar parameter inequalities. -/
lemma balanced_word_sum_bound {n : ℕ} (hn : 4 ≤ n) {α β ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hαN : α⁻¹ ≤ Real.sqrt (n : ℝ))
    (hβ : 0 ≤ β) (hβupper : β ≤ α ^ rho n * Real.exp ε)
    (hscale : α ^ (-(1 + rho n)) ≤ (n : ℝ))
    (hε : 0 ≤ ε) (hεN : ε * (n : ℝ) ≤ Real.sqrt (n : ℝ)) :
    (∑ w : Fin n → Bool,
      IsolatedWeight.weight (BalancedSchedule.internalEdges n)
        (Finset.univ.filter (fun i => balancedLayer hn i = true))
        BalancedSchedule.adjacent α⁻¹ β ((n : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt (n : ℝ)) := by
  classical
  cases n with
  | zero => omega
  | succ n =>
    apply balanced_word_sum_bound_of_product hn α⁻¹ β (ε * ((n + 1 : ℕ) : ℝ))
      ((one_le_inv₀ hα).2 hα1) hαN hβ hεN
    intro w
    apply RunLayerWeights.count_weight_le_exp_mul_runCount w
      (Finset.univ.filter (fun i => balancedLayer hn i = true))
      hα hα1 hβ hε hβupper hscale
    intro b hb
    simpa using (balancedLayer_infix_discrepancy hn b hb).le

end Problem335.LowerParameters

end

end OAI
