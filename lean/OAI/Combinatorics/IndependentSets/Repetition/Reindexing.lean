import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Sampling

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

def reindexEquiv {ι κ Ω : Type*} (e : κ ≃ ι) : (ι → Ω) ≃ (κ → Ω) where
  toFun f := f ∘ e
  invFun g := g ∘ e.symm
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

theorem table_const_reindex {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
    (μ : FiniteDistribution Ω) (e : κ ≃ ι) :
    (table (fun _ : ι => μ)).pushforward (fun f => f ∘ e) =
      table (fun _ : κ => μ) := by
  classical
  change (table (fun _ : ι => μ)).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : ι, μ.weight (g (e.symm i))) = ∏ k : κ, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

theorem iid_reindex {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {n m : Nat} (e : Fin m ≃ Fin n) :
    (μ.iid n).pushforward (fun f => f ∘ e) = μ.iid m := by
  classical
  change (μ.iid n).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : Fin n, μ.weight (g (e.symm i))) = ∏ k : Fin m, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

theorem probability_reindex_of_weight {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (e : Ω ≃ Γ)
    (hweight : ∀ x, ν.weight (e x) = μ.weight x) (event : Γ → Bool) :
    ν.probability event = μ.probability (fun x => event (e x)) := by
  classical
  change (∑ y, if event y then ν.weight y else 0) =
    ∑ x, if event (e x) then μ.weight x else 0
  rw [← e.sum_comp (fun y => if event y then ν.weight y else 0)]
  apply Finset.sum_congr rfl
  intro x _
  rw [hweight]

end FiniteDistribution

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def questionReindexEquiv {n m : Nat} (e : Fin m ≃ Fin n) :
    ((Fin n → Q₁) × (Fin n → Q₂)) ≃ ((Fin m → Q₁) × (Fin m → Q₂)) :=
  Equiv.prodCongr (FiniteDistribution.reindexEquiv e)
    (FiniteDistribution.reindexEquiv e)

def reindexStrategy {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    Strategy (Fin m → Q₁) (Fin m → Q₂) (Fin m → A₁) (Fin m → A₂) :=
  (fun x i => s.1 (x ∘ e.symm) (e i),
   fun y i => s.2 (y ∘ e.symm) (e i))

theorem repetition_question_weight_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition m).questions.weight (questionReindexEquiv e q) =
      (G.repetition n).questions.weight q := by
  classical
  rw [repetition_question_weight, repetition_question_weight]
  change (∏ i : Fin m, G.questions.weight (q.1 (e i), q.2 (e i))) =
    ∏ j : Fin n, G.questions.weight (q.1 j, q.2 j)
  exact e.prod_comp (fun j => G.questions.weight (q.1 j, q.2 j))

theorem repetition_questions_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n) :
    (G.repetition n).questions.pushforward (questionReindexEquiv e) =
      (G.repetition m).questions := by
  classical
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  change (G.repetition n).questions.weight ((questionReindexEquiv e).symm q) =
    (G.repetition m).questions.weight q
  have h := repetition_question_weight_reindex G e ((questionReindexEquiv e).symm q)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem coordinateWin_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (i : Fin m) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.coordinateWin (reindexStrategy e s) i (questionReindexEquiv e q) =
      G.coordinateWin s (e i) q := by
  have h₁ : (fun j : Fin n => q.1 (e (e.symm j))) = q.1 := by
    funext j
    rw [e.apply_symm_apply]
  have h₂ : (fun j : Fin n => q.2 (e (e.symm j))) = q.2 := by
    funext j
    rw [e.apply_symm_apply]
  change G.accepts (q.1 (e i)) (q.2 (e i))
      (s.1 (fun j => q.1 (e (e.symm j))) (e i))
      (s.2 (fun j => q.2 (e (e.symm j))) (e i)) =
    G.accepts (q.1 (e i)) (q.2 (e i)) (s.1 q.1 (e i)) (s.2 q.2 (e i))
  rw [h₁, h₂]

theorem selectedWins_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) (q : (Fin n → Q₁) × (Fin n → Q₂)) :
    G.selectedWins (reindexStrategy e s) S (questionReindexEquiv e q) =
      G.selectedWins s (S.map e.toEmbedding) q := by
  classical
  unfold selectedWins
  congr 1
  apply propext
  constructor
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    have hw := h i hi
    rw [coordinateWin_reindex] at hw
    exact hw
  · intro h i hi
    rw [coordinateWin_reindex]
    exact h (e i) (Finset.mem_map.mpr ⟨i, hi, rfl⟩)

theorem selectedSuccess_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (S : Finset (Fin m)) :
    G.selectedSuccess (reindexStrategy e s) S =
      G.selectedSuccess s (S.map e.toEmbedding) := by
  classical
  unfold selectedSuccess
  rw [FiniteDistribution.probability_reindex_of_weight
    (G.repetition n).questions (G.repetition m).questions (questionReindexEquiv e)
    (repetition_question_weight_reindex G e)]
  congr 1
  funext q
  exact selectedWins_reindex G e s S q

theorem repetition_success_reindex (G : Game Q₁ Q₂ A₁ A₂)
    {n m : Nat} (e : Fin m ≃ Fin n)
    (s : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    (G.repetition m).success (reindexStrategy e s) =
      (G.repetition n).success s := by
  classical
  have huniv : (Finset.univ : Finset (Fin m)).map e.toEmbedding = Finset.univ := by
    ext j
    constructor
    · intro _
      exact Finset.mem_univ j
    · intro _
      exact Finset.mem_map.mpr ⟨e.symm j, Finset.mem_univ _, e.apply_symm_apply j⟩
  have h := selectedSuccess_reindex G e s Finset.univ
  rw [huniv, selectedSuccess_univ, selectedSuccess_univ] at h
  exact h

end Game
end IndependentSetsGames.Foundations.Games
end

end OAI
