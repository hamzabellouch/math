import OAI.Combinatorics.GraphThreshold.GraphEncoding
import Mathlib.Tactic

namespace OAI

noncomputable section

namespace LeanBlast.SecondKahnKalai

section BernoulliEndpoints

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliWeight_zero (W : Finset X) :
    bernoulliWeight 0 W = if W = ∅ then 1 else 0 := by
  by_cases hW : W = ∅
  · subst W
    simp [bernoulliWeight]
  · rw [ite_eq_right hW]
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hW
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

theorem bernoulliWeight_one (W : Finset X) :
    bernoulliWeight 1 W = if W = Finset.univ then 1 else 0 := by
  by_cases hW : W = Finset.univ
  · subst W
    simp [bernoulliWeight]
  · rw [ite_eq_right hW]
    obtain ⟨x, hx⟩ : ∃ x : X, x ∉ W := by
      simpa [Finset.eq_univ_iff_forall] using hW
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])

@[simp]
theorem bernoulliExpectation_zero (f : Finset X → ℝ) :
    bernoulliExpectation 0 f = f ∅ := by
  simp [bernoulliExpectation, bernoulliWeight_zero]

@[simp]
theorem bernoulliExpectation_one (f : Finset X → ℝ) :
    bernoulliExpectation 1 f = f Finset.univ := by
  simp [bernoulliExpectation, bernoulliWeight_one]

@[simp]
theorem bernoulliProbability_zero (P : Finset X → Prop) [DecidablePred P] :
    bernoulliProbability 0 P = if P ∅ then 1 else 0 := by
  classical
  unfold bernoulliProbability
  rw [Finset.sum_eq_single ∅]
  · simp [bernoulliWeight_zero]
  · intro W _ hW
    simp [bernoulliWeight_zero, hW]
  · simp

@[simp]
theorem bernoulliProbability_one (P : Finset X → Prop) [DecidablePred P] :
    bernoulliProbability 1 P = if P Finset.univ then 1 else 0 := by
  classical
  unfold bernoulliProbability
  rw [Finset.sum_eq_single Finset.univ]
  · simp [bernoulliWeight_one]
  · intro W _ hW
    simp [bernoulliWeight_one, hW]
  · simp

end BernoulliEndpoints

theorem copyCount_iso_target {V W U : Type*} [Fintype V]
    (G : SimpleGraph V) {H : SimpleGraph W} {F : SimpleGraph U}
    (e : H ≃g F) : G.copyCount H = G.copyCount F := by
  classical
  unfold SimpleGraph.copyCount
  congr 1
  apply Finset.filter_congr
  intro J _
  constructor
  · rintro ⟨g⟩
    exact ⟨g.comp e.symm⟩
  · rintro ⟨g⟩
    exact ⟨g.comp e⟩

theorem expectedCopies_iso {V W : Type*} (n : ℕ) (p : ℝ)
    {H : SimpleGraph V} {F : SimpleGraph W} (e : H ≃g F) :
    expectedCopies n p H = expectedCopies n p F := by
  unfold expectedCopies bernoulliExpectation
  simp_rw [copyCount_iso_target _ e]

theorem containmentProbability_iso {V W : Type*} (n : ℕ) (p : ℝ)
    {H : SimpleGraph V} {F : SimpleGraph W} (e : H ≃g F) :
    containmentProbability n p H = containmentProbability n p F := by
  unfold containmentProbability
  congr 1
  funext K
  rw [copyCount_iso_target _ e]

theorem isContained_top_of_card_le {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    H.IsContained (⊤ : SimpleGraph (Fin n)) := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card V ≤ Fintype.card (Fin n) by simpa using hcard)
  refine ⟨{ toHom := ⟨f, ?_⟩, injective' := f.injective }⟩
  intro a b hab
  exact f.injective.ne hab.ne

theorem expectedCopies_one_ge_one {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    1 ≤ expectedCopies n 1 H := by
  have hp : 0 < (⊤ : SimpleGraph (Fin n)).copyCount H :=
    SimpleGraph.copyCount_pos.mpr (isContained_top_of_card_le n H hcard)
  simpa only [expectedCopies, bernoulliExpectation_one, graphOfEdges_univ,
    Nat.one_le_cast] using Nat.succ_le_of_lt hp

theorem containmentProbability_one {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (hcard : Fintype.card V ≤ n) :
    containmentProbability n 1 H = 1 := by
  classical
  have hp : 0 < (⊤ : SimpleGraph (Fin n)).copyCount H :=
    SimpleGraph.copyCount_pos.mpr (isContained_top_of_card_le n H hcard)
  simp only [containmentProbability, bernoulliProbability_one, graphOfEdges_univ, hp,
    ite_true]

theorem copyCount_bot_of_edge {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (he : 1 ≤ edgeCount H) :
    (⊥ : SimpleGraph W).copyCount H = 0 := by
  apply SimpleGraph.copyCount_eq_zero.mpr
  rintro ⟨f⟩
  have hbot : H = ⊥ := by
    apply SimpleGraph.eq_bot_iff_forall_not_adj.mpr
    intro a b hab
    exact f.toHom.map_adj hab
  have hz := (edgeCount_eq_zero_iff H).mpr hbot
  omega

theorem expectedCopies_zero {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (he : 1 ≤ edgeCount H) :
    expectedCopies n 0 H = 0 := by
  simp [expectedCopies, copyCount_bot_of_edge H he]

theorem containmentProbability_zero {V : Type*} [Fintype V] (n : ℕ)
    (H : SimpleGraph V) (he : 1 ≤ edgeCount H) :
    containmentProbability n 0 H = 0 := by
  classical
  simp only [containmentProbability, bernoulliProbability_zero, graphOfEdges_empty,
    copyCount_bot_of_edge H he, lt_self_iff_false, ite_false]

end LeanBlast.SecondKahnKalai

end

end OAI
