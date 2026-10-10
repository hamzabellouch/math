import OAI.Probability.MatroidProphet.Main
import OAI.Probability.MatroidSecretary.Accounting.MainFeasibilityContract
import OAI.Probability.MatroidSecretary.Selection.FeasibilitySpec
import OAI.Probability.MatroidSecretary.Selection.GreedyExecution

namespace OAI

/-! Complete source contract for `algorithm.tex`, `lem:feasibility` (lines
179--183; source SHA256 b702fa1da832d3cbebcf5a70f0b0e9505b3423e2ed9884c22fe4194ba4974fbe).
The actual main rule is used, not an abstract feasible-rule hypothesis. -/

namespace MatroidProphet
namespace FeasibilityContract
open Set Finset MeasureTheory

/-- Hidden observations depend only on the initially sacrificed coordinates. -/
theorem observed_eq_of_eq_on_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w w' : Weights n)
    (h : ∀ e ∈ A.mask r, w e = w' e) :
    observed A r w = observed A r w' := by
  classical
  funext e
  by_cases he : e ∈ A.mask r
  · simp only [observed, ite_eq_left he, h e he]
  · simp only [observed, ite_eq_right he]

/-- Hidden execution is nonanticipating: equal initial observations and equal
revealed histories force equal current decisions, irrespective of future data. -/
theorem hidden_decision_congr {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w w' : Weights n) (π π' : ArrivalOrder n) (k : Fin n)
    (hmask : ∀ e ∈ A.mask r, w e = w' e)
    (hhist : history w π k = history w' π' k) :
    decisionAt A.core r (observed A r w) w π k =
      decisionAt A.core r (observed A r w') w' π' k := by
  rw [observed_eq_of_eq_on_mask A r w w' hmask]
  exact decisionAt_congr A.core r (observed A r w') w w' π π' k hhist

/-- Sacrificing the fixed mask preserves irrevocability. -/
theorem hiddenAcceptedThrough_mono {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n)
    {t t' : ℕ} (h : t ≤ t') :
    hiddenAcceptedThrough A r w π t ⊆ hiddenAcceptedThrough A r w π t' := by
  intro e he
  obtain ⟨he, hm⟩ := Finset.mem_sdiff.mp he
  exact Finset.mem_sdiff.mpr
    ⟨acceptedThrough_mono A.core r (observed A r w) w π h he, hm⟩

/-- No sacrificed observation label is ever accepted. -/
theorem hiddenAcceptedThrough_disjoint_mask {n bits : ℕ} (A : HiddenRule n bits)
    (r : Seed bits) (w : Weights n) (π : ArrivalOrder n) (t : ℕ) :
    Disjoint (hiddenAcceptedThrough A r w π t) (A.mask r) := by
  apply Finset.disjoint_left.mpr
  intro e he hm
  exact (Finset.mem_sdiff.mp he).2 hm

/-- All parts of the manuscript's feasibility and information contract for the
actual layered main algorithm. Empty ground sets, loops, zero weights, ties,
and empty group lists remain within the quantified input domain. -/
theorem main_rule {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ) :
    (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      ∀ (r : Seed (mainSeedBits n)) (π : ArrivalOrder n) (t : ℕ),
        M.Indep (hiddenAcceptedThrough (MainAlgorithm.hidden M hE) r w π t : Set (Fin n))) ∧
    (∀ k, Measurable
      (fun x : Seed (mainSeedBits n) × (Weights n × History n k) =>
        (MainAlgorithm.core M hE).decide k x.1 x.2.1 x.2.2)) ∧
    (∀ (r : Seed (mainSeedBits n)) (w w' : Weights n)
      (π π' : ArrivalOrder n) (k : Fin n),
      (∀ e ∈ (MainAlgorithm.hidden M hE).mask r, w e = w' e) →
      history w π k = history w' π' k →
      decisionAt (MainAlgorithm.core M hE) r
          (observed (MainAlgorithm.hidden M hE) r w) w π k =
        decisionAt (MainAlgorithm.core M hE) r
          (observed (MainAlgorithm.hidden M hE) r w') w' π' k) ∧
    (∀ (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n)
      (t t' : ℕ), t ≤ t' →
      hiddenAcceptedThrough (MainAlgorithm.hidden M hE) r w π t ⊆
        hiddenAcceptedThrough (MainAlgorithm.hidden M hE) r w π t') ∧
    (∀ (r : Seed (mainSeedBits n)) (w : Weights n) (π : ArrivalOrder n) (t : ℕ),
      Disjoint (hiddenAcceptedThrough (MainAlgorithm.hidden M hE) r w π t)
        ((mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C)) := by
  refine ⟨MainAlgorithm.hidden_feasible M hE, ?_, ?_, ?_, ?_⟩
  · exact (MainAlgorithm.core M hE).measurable_decide
  · exact hidden_decision_congr (MainAlgorithm.hidden M hE)
  · intro r w π t t' ht
    exact hiddenAcceptedThrough_mono (MainAlgorithm.hidden M hE) r w π ht
  · exact hiddenAcceptedThrough_disjoint_mask (MainAlgorithm.hidden M hE)

/-- The empty listed-group case cannot assign any arriving label to a layer. -/
theorem assign_none_of_groups_nil {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (d : MainMasks n) (seen : Fin n → Option ℤ)
    (hg : MainAlgorithm.groups M d seen = []) (e : Fin n) (w : Option ℤ) :
    MainAlgorithm.assign M hE d seen e w = none := by
  classical
  cases w with
  | none => rfl
  | some i =>
    have hn : ¬ MainAlgorithm.eligible M hE d seen e i := by
      intro he
      simpa [hg] using he.2.2.1
    simp [MainAlgorithm.assign, hn]

/-- Zero weights do not enter a logarithm and are assigned no layer. -/
theorem assign_zero {n : ℕ} (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (seen : Fin n → Option ℤ) (e : Fin n) :
    MainAlgorithm.assign M hE d seen e (roundedLevel weightBase 0) = none := by
  simp [roundedLevel, MainAlgorithm.assign]

/-- A loop can never pass the actual candidate test, regardless of priorities. -/
theorem not_candidate_of_loop {n : ℕ} (M : Matroid (Fin n)) (d : MainMasks n)
    (seen : Fin n → Option ℤ) (e : Fin n) (w : Option ℤ)
    (he : e ∈ M.closure ∅) : ¬ MainAlgorithm.candidate M d seen e w := by
  intro hc
  exact hc.2.2 (M.closure_subset_closure (Set.empty_subset _) he)

/-- The complete required `lem:feasibility` contract, for the concrete source rule. -/
theorem source_main_feasibility {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) : MainRuleFeasibility M (MainAlgorithm.hidden M hE) :=
  MainAlgorithm.source_feasibility_contract M hE

end FeasibilityContract
end MatroidProphet

end OAI
