import OAI.Algebra.DepthFive.RunWeights
import OAI.Algebra.DepthFive.RunSum
import OAI.Algebra.DepthFive.RunLayerWeights
import OAI.Algebra.DepthFive.IsolatedFlip
import OAI.Algebra.DepthFive.IsolatedWeight

namespace OAI

/-! Assembly of the numeric and finite-word estimates in the path-type sum.
The remaining application-specific hypotheses describe the actual path weights. -/

open scoped BigOperators
noncomputable section

namespace Problem335
namespace WordSum

/-- Combine exact smoothing fibers, surviving local corrections, and interior-run counting. -/
lemma corrected_sum_le_exp_of_sum (n k : ℕ) (a c : ℝ)
    (S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : ∀ i ∈ S, ∀ j, R i j → j ∉ S)
    (hcard : S.card ≤ k)
    (hk : 2 * (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (ha : 0 ≤ a) (haN : a ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hc : 0 ≤ c) (hcN : c ≤ 2 / (((n + 1 : ℕ) : ℝ) ^ 2))
    (W Z : (Fin (n + 1) → Bool) → ℝ)
    (hWnonneg : ∀ w, 0 ≤ W w) (hZnonneg : ∀ w, 0 ≤ Z w)
    (hratio : ∀ w, W w = W (IsolatedFlip.flip S R w) *
      c ^ (IsolatedFlip.removed S R w).card)
    (hfixed : ∀ w, IsolatedFlip.flip S R w = w →
      W w ≤ (1 + a) * (1 + a / ((n + 1 : ℕ) : ℝ)) ^ k * Z w)
    (hZbound : (∑ w, Z w) ≤ Real.exp (5 * Real.sqrt ((n + 1 : ℕ) : ℝ))) :
    (∑ w, W w) ≤ Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let Q : ℝ := (1 + a) * (1 + a / N) ^ k
  have hN : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hNpos : 0 < N := by linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hZsum : 0 ≤ ∑ w, Z w := Finset.sum_nonneg (fun w _ => hZnonneg w)
  have hfixedsum :
      (∑ w ∈ Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w), W w) ≤
        Q * ∑ w, Z w := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : IsolatedFlip.flip S R w = w
    · rw [ite_eq_left hw]
      exact hfixed w hw
    · rw [ite_eq_right hw]
      exact mul_nonneg hQ (hZnonneg w)
  have hcpow : (1 + c) ^ S.card ≤ (1 + 2 / N ^ 2) ^ k := by
    calc
      (1 + c) ^ S.card ≤ (1 + 2 / N ^ 2) ^ S.card := by gcongr
      _ ≤ (1 + 2 / N ^ 2) ^ k := by
        exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hcard
  have hpref : (1 + 2 / N ^ 2) ^ k * Q ≤ Real.exp (3 * Real.sqrt N) := by
    dsimp [Q]
    rw [← mul_assoc]
    exact RunWeights.correction_prefactor_le_exp hN ha haN k hk
  change (∑ w, W w) ≤ Real.exp (8 * Real.sqrt N)
  calc
    (∑ w, W w) ≤ (1 + c) ^ S.card *
        ∑ w ∈ Finset.univ.filter (fun w => IsolatedFlip.flip S R w = w), W w :=
      IsolatedFlip.correction_removal hS c hc W hWnonneg hratio
    _ ≤ (1 + c) ^ S.card * (Q * ∑ w, Z w) := by gcongr
    _ ≤ (1 + 2 / N ^ 2) ^ k * (Q * ∑ w, Z w) := by gcongr
    _ = ((1 + 2 / N ^ 2) ^ k * Q) * ∑ w, Z w := by ring
    _ ≤ Real.exp (3 * Real.sqrt N) * Real.exp (5 * Real.sqrt N) := by gcongr
    _ = Real.exp (8 * Real.sqrt N) := by rw [← Real.exp_add]; congr 1; ring

/-- The actual word weights satisfy the square-root exponential bound once
run intervals and the surviving coincidence corrections have been estimated. -/
lemma sum_actual_weight_le_exp (n : ℕ) (A B E : ℝ)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)) (hB : 0 ≤ B)
    (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ (V.filter fun i => w i = true).card *
        B ^ ((Finset.univ \ V).filter fun i => w i = true).card ≤
          Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w)
    (hcorr : ∀ w, IsolatedFlip.flip S R w = w →
      IsolatedWeight.correction V R A (((n + 1 : ℕ) : ℝ)⁻¹) w ≤
        (1 + A) * (1 + A / ((n + 1 : ℕ) : ℝ)) ^ V.card) :
    (∑ w, IsolatedWeight.weight edges V R A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  classical
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let F : (Fin (n + 1) → Bool) → ℝ := fun w =>
    A ^ (V.filter fun i => w i = true).card *
      B ^ ((Finset.univ \ V).filter fun i => w i = true).card
  let Z : (Fin (n + 1) → Bool) → ℝ := fun w =>
    N⁻¹ ^ (WordSwitches.switches w).card * F w
  let W := IsolatedWeight.weight edges V R A B N⁻¹
  let c : ℝ := N⁻¹ ^ 2 * (1 + A) / A
  have hN : 0 < N := by dsimp [N]; positivity
  have hApos : 0 < A := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcN : c ≤ 2 / N ^ 2 := by
    have hr : (1 + A) / A ≤ 2 := (div_le_iff₀ hApos).2 (by linarith)
    calc
      c = N⁻¹ ^ 2 * ((1 + A) / A) := by dsimp [c]; ring
      _ ≤ N⁻¹ ^ 2 * 2 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 2 / N ^ 2 := by rw [inv_pow]; ring
  have hW : ∀ w, 0 ≤ W w :=
    IsolatedWeight.weight_nonneg edges V R hApos.le hB (by positivity)
  have hZ : ∀ w, 0 ≤ Z w := by intro w; dsimp [Z, F]; positivity
  have hZsum : (∑ w, Z w) ≤ Real.exp (5 * Real.sqrt N) := by
    have hh := RunSum.sum_weighted_switch_penalty_le_exp n E F hprod
    exact hh.trans (Real.exp_le_exp.mpr (by change E + 4 * Real.sqrt N ≤ _; linarith))
  apply corrected_sum_le_exp_of_sum n V.card A c S R
  · intro i hi j hij hj
    exact hV i (hS hi) j hij (hS hj)
  · exact Finset.card_le_card hS
  · exact hcard
  · exact hApos.le
  · exact hAN
  · exact hc
  · exact hcN
  · exact hW
  · exact hZ
  · intro w
    exact IsolatedWeight.weight_flip hS hV hR hdegree hApos.ne' B N⁻¹ w
  · intro w hw
    have hh := mul_le_mul_of_nonneg_left (hcorr w hw) (hZ w)
    dsimp [W, IsolatedWeight.weight, Z, F] at hh ⊢
    rw [hswitch]
    nlinarith [hh]
  · exact hZsum

/-- Full corrected-word bound with the actual fixed-word correction estimate discharged.
Only the graph structure and the per-word product-of-runs estimate remain as inputs. -/
lemma sum_actual_weight_le_exp_of_endpoints (n : ℕ) (A B E : ℝ)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hend : (V \ S).card ≤ 1)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hA : 1 ≤ A) (hAN : A ≤ Real.sqrt ((n + 1 : ℕ) : ℝ)) (hB : 0 ≤ B)
    (hE : E ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hprod : ∀ w : Fin (n + 1) → Bool,
      A ^ (V.filter fun i => w i = true).card *
        B ^ ((Finset.univ \ V).filter fun i => w i = true).card ≤
          Real.exp E * ((n + 1 : ℕ) : ℝ) ^ WordRuns.runCount w) :
    (∑ w, IsolatedWeight.weight edges V R A B (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  apply sum_actual_weight_le_exp n A B E edges V S R hS hV hR hdegree hswitch
    hcard hA hAN hB hE hprod
  intro w hw
  have hN : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simpa only [div_eq_mul_inv] using IsolatedWeight.correction_le_endpoint_bound
    hS hend hw (show 0 ≤ A by linarith) (by positivity)
    (inv_le_one_of_one_le₀ hN)

/-- An interval-balanced independent layer partition gives the full word-sum estimate.
This version has no assumed rank, trace, weight, or run-product inequalities. -/
lemma sum_weight_le_exp_of_discrepancy (n : ℕ) (α β ρ ε : ℝ)
    (edges : Finset (Fin (n + 1) × Fin (n + 1)))
    (V S : Finset (Fin (n + 1))) (R : Fin (n + 1) → Fin (n + 1) → Prop)
    (hS : S ⊆ V) (hV : ∀ i ∈ V, ∀ j, R i j → j ∉ V)
    (hR : ∀ e ∈ edges, R e.1 e.2 ∧ R e.2 e.1)
    (hdegree : ∀ i ∈ S, SwitchRestoration.endpointDegree edges i = 2)
    (hswitch : ∀ w, SwitchRestoration.switchCount edges w = (WordSwitches.switches w).card)
    (hend : (V \ S).card ≤ 1)
    (hcard : 2 * (V.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ))
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hρ : ρ ≤ 1) (hε : 0 ≤ ε)
    (hαN : α⁻¹ ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hβupper : β ≤ α ^ ρ * Real.exp ε)
    (hεN : ε * ((n + 1 : ℕ) : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ))
    (hdiscrepancy : ∀ b : List (Fin (n + 1)), b <:+: List.ofFn id →
      (b.countP (fun i => decide (i ∈ V)) : ℝ) -
        ρ * b.countP (fun i => !decide (i ∈ V)) ≤ 1 + ρ) :
    (∑ w, IsolatedWeight.weight edges V R α⁻¹ β (((n + 1 : ℕ) : ℝ)⁻¹) w) ≤
      Real.exp (8 * Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
  have hA : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
  apply sum_actual_weight_le_exp_of_endpoints n α⁻¹ β (ε * ((n + 1 : ℕ) : ℝ))
    edges V S R hS hV hR hdegree hswitch hend hcard hA hαN hβ hεN
  intro w
  exact RunLayerWeights.count_weight_le_exp_mul_runCount w V hα hα1 hβ hε hβupper
    (RunWeights.scale_le_of_inv_le_sqrt hα hα1 hρ (by positivity) hαN) hdiscrepancy

end WordSum
end Problem335

end

end OAI
