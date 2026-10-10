import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Transport.InformationRestriction
import Mathlib.Combinatorics.Matroid.Loop

namespace OAI

/-!
# Source-facing feasibility and information contract

Pinned source: `sections/algorithm.tex`, Lemma `lem:feasibility`, lines 179–204.
The rule here is the actual main rule, not an abstract feasible substitute.
The first component gives prefix feasibility. The remaining components make
measurability, the permitted observations, irrevocability, and sacrifice explicit.
None of these components assumes a source theorem or any algorithm-validity axiom.
-/

namespace MatroidProphet.MainAlgorithm

/-- Full feasibility/information content of the manuscript's main-rule lemma. -/
theorem source_feasibility_contract {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) :
    Feasible M (core M hE) ∧
    (∀ k : Fin n, Measurable
      (fun x : Seed (mainSeedBits n) × (Weights n × History n k) =>
        (hidden M hE).core.decide k x.1
          (observed (hidden M hE) x.1 x.2.1) x.2.2)) ∧
    (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed (mainSeedBits n)) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough (hidden M hE) r w π t : Set (Fin n))) ∧
    (∀ (r : Seed (mainSeedBits n)) (w w' : Weights n)
      (π π' : ArrivalOrder n) (t : ℕ),
      (∀ e ∈ (hidden M hE).mask r, w e = w' e) →
      (∀ j : Fin n, j.val < t →
        (π j, w (π j)) = (π' j, w' (π' j))) →
      hiddenAcceptedThrough (hidden M hE) r w π t =
        hiddenAcceptedThrough (hidden M hE) r w' π' t) ∧
    (∀ (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n),
      Monotone (hiddenAcceptedThrough (hidden M hE) r w π)) ∧
    (∀ (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) (t : ℕ),
      Disjoint (hiddenAcceptedThrough (hidden M hE) r w π t)
        ((mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C)) := by
  refine ⟨core_feasible M hE, ?_, hidden_feasible M hE, ?_, ?_, ?_⟩
  · exact measurable_hidden_core_decide (hidden M hE)
  · exact hiddenAcceptedThrough_eq_of_same_information (hidden M hE)
  · exact hiddenAcceptedThrough_monotone (hidden M hE)
  · exact hiddenAcceptedThrough_disjoint_mask (hidden M hE)

/-- Loops are never selected, including when their weights have no moment bound. -/
theorem source_accepted_isNonloop {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (w : Weights n) (hw : ∀ e, 0 ≤ w e)
    (r : Seed (mainSeedBits n)) (π : ArrivalOrder n) (t : ℕ) (e : Fin n)
    (he : e ∈ hiddenAcceptedThrough (hidden M hE) r w π t) :
    M.IsNonloop e :=
  (hidden_feasible M hE w hw r π t).isNonloop_of_mem he

/-- The disclosed mask is determined by the initial seed, with no weight input. -/
theorem source_observation_mask {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) :
    (hidden M hE).mask r = (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C := rfl

/-- Loops fail the candidate test before the layer selection is attempted. -/
theorem source_loop_not_candidate {n : ℕ} (M : Matroid (Fin n))
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) (level : Option ℤ)
    (he : e ∈ M.closure ∅) : ¬ candidate M d seen e level := by
  intro hc
  exact hc.2.2 (M.closure_mono (Set.empty_subset _) he)

/-- Zero (and negative off-domain) values never receive an eligible layer. -/
theorem source_nonpositive_unassigned {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (e : Fin n) (x : ℝ) (hx : x ≤ 0) :
    assign M hE d seen e (roundedLevel weightBase x) = none := by
  simp only [roundedLevel, ite_eq_right (not_lt.mpr hx), assign]

/-- An empty listed-group collection assigns no arriving value to a layer. -/
theorem source_empty_groups_unassigned {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (hg : groups M d seen = []) (e : Fin n) (level : Option ℤ) :
    assign M hE d seen e level = none := by
  classical
  cases level <;> simp [assign, eligible, hg]

end MatroidProphet.MainAlgorithm

end OAI
