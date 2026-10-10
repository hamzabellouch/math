import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace KServer

universe u

abbrev Configuration (k : ℕ) (X : Type u) := Fin k → X

def LabelDistribution (k : ℕ) :=
  {probability : Fin k → ℝ //
    (∀ label, 0 ≤ probability label) ∧ ∑ label, probability label = 1}

abbrev Policy (k : ℕ) (X : Type u) :=
  List (X × Fin k) → X → LabelDistribution k

def serve {k : ℕ} {X : Type u} (s : Configuration k X)
    (label : Fin k) (request : X) : Configuration k X :=
  Function.update s label request

def serviceCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) : (requests : List X) → (Fin requests.length → Fin k) → ℝ
  | [], _ => 0
  | request :: requests, labels =>
      dist (s (labels 0)) request +
        serviceCost (serve s (labels 0) request) requests (fun index => labels index.succ)

def pathProbability {k : ℕ} {X : Type u} (A : Policy k X)
    (history : List (X × Fin k)) :
    (requests : List X) → (Fin requests.length → Fin k) → ℝ
  | [], _ => 1
  | request :: requests, labels =>
      (A history request).val (labels 0) *
        pathProbability A (history ++ [(request, labels 0)]) requests
          (fun index => labels index.succ)

def expectedCost {k : ℕ} {X : Type u} [MetricSpace X]
    (A : Policy k X) (s : Configuration k X) (requests : List X) : ℝ :=
  ∑ labels : Fin requests.length → Fin k,
    pathProbability A [] requests labels * serviceCost s requests labels

def optimalCost {k : ℕ} {X : Type u} [MetricSpace X]
    (s : Configuration k X) (requests : List X) : ℝ :=
  sInf (Set.range (serviceCost s requests))

def MainStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ), 2 ≤ k →
    ∀ (X : Type u) (_ : MetricSpace X),
      (∃ embedding : Fin (k + 1) → X, Function.Injective embedding) →
      ∀ s : Configuration k X,
        ∃ A : Policy k X, ∃ B : ℝ,
          0 ≤ B ∧ (Function.Injective s → B = 0) ∧
          ∀ requests : List X,
            expectedCost A s requests ≤
              C * (Real.log (k + 1)) ^ 2 * optimalCost s requests + B

theorem main_theorem : MainStatement.{u} := by
  sorry

end KServer

end

end OAI
