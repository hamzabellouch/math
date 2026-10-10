import OAI.NumberTheory.DukePrimeDegree.Entropy.SparseObservationEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.EncodedObservationEntropy

namespace OAI

/-! # Small Shannon entropy for the last-active-scale observation -/

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal
namespace DukePrimeDegree

lemma countable_observation_distribution
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsProbabilityMeasure μ] (P : Y → α)
    (hP : ∀ a, MeasurableSet {x | P x=a}) :
    Summable (fun a => μ.real {x | P x=a}) ∧
      (∑' a, μ.real {x | P x=a})=1 := by
  have hdis : Pairwise (Disjoint on (fun a => {x | P x=a})) := by
    intro a b hab
    exact disjoint_left.mpr fun x hx hy => hab (hx.symm.trans hy)
  have hcover : (⋃ a, {x | P x=a})=univ := by ext x; simp
  have hsum : (∑' a, μ {x | P x=a})=1 := by
    rw [←measure_iUnion hdis hP,hcover,measure_univ]
  refine ⟨ENNReal.summable_toReal (by rw [hsum]; exact ENNReal.one_ne_top),?_⟩
  change (∑' a, (μ {x | P x=a}).toReal)=1
  rw [←ENNReal.tsum_toReal_eq (fun _ => measure_ne_top μ _),hsum,ENNReal.toReal_one]

/-- All grid sizes are fixed before the section masses are chosen. -/
theorem exists_lastActiveObservation_entropy_budget
    {Y : Type*} [MeasurableSpace Y] (K : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Summable δ ∧ (∑' n, δ n) ≤ ε/4 ∧
      ∀ (μ : Measure Y) [IsProbabilityMeasure μ] (S : ℕ → Set Y),
        (∀ n, MeasurableSet (S n)) → (∀ n, μ.real (S n) ≤ δ n) →
        ∀ B : ∀ n, Y → Fin (K n), (∀ n, Measurable (B n)) →
          Summable (fun z => Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) ∧
          (∑' z, Real.negMulLog (μ.real {x | lastActiveObservation S B x=z})) < ε := by
  obtain ⟨δ,hδ,hδs,hδsum,H⟩ := exists_sparse_distribution_budget K hε
  refine ⟨δ,hδ,hδs,hδsum,?_⟩
  intro μ _ S hS hsmall B hB
  let I := Option (Σ n : ℕ, Fin (K n))
  let : MeasurableSpace I := ⊤
  let P := lastActiveObservation S B
  have hP : Measurable P := measurable_lastActiveObservation hS B hB
  have hdist := countable_observation_distribution μ P (fun z => hP (measurableSet_singleton z))
  apply H (fun z => μ.real {x | P x=z}) (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) hdist.1 hdist.2
  intro n i
  apply (measureReal_mono (s₁ := {x | P x=some ⟨n,i⟩}) (s₂ := S n) ?_
    (measure_ne_top μ _)).trans (hsmall n)
  intro x hx
  have hx' : x ∈ lastActiveObservationAtom S B (some ⟨n,i⟩) := by
    rw [←lastActiveObservation_fiber]
    exact hx
  exact hx'.1.1

end DukePrimeDegree

end

end OAI
