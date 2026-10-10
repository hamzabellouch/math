import OAI.Probability.InvariantIsing.Core.FiniteSpinEntropy

namespace OAI

/-! Exact finite pushforward weights and their entropy averages. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def finitePushforwardWeights {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (y : Y) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = y), p x

lemma finitePushforwardWeights_nonneg {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (y : Y) :
    0 ≤ finitePushforwardWeights f p y :=
  Finset.sum_nonneg (fun x _ => hp x)

lemma finitePushforwardWeights_sum {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) : ∑ y, finitePushforwardWeights f p y = ∑ x, p x :=
  Finset.sum_fiberwise Finset.univ f p

lemma finitePushforwardWeights_at_image {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (x : X) :
    p x ≤ finitePushforwardWeights f p (f x) :=
  Finset.single_le_sum (fun y _ => hp y) (by simp)

lemma finitePushforwardWeights_average {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (F : Y → ℝ) :
    (∑ y, finitePushforwardWeights f p y * F y) = ∑ x, p x * F (f x) := by
  simp only [finitePushforwardWeights, Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => p x * F (f x))]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

lemma finitePushforwardWeights_entropy {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) :
    finiteShannonEntropy (finitePushforwardWeights f p) =
      -∑ x, p x * Real.log (finitePushforwardWeights f p (f x)) := by
  rw [finiteShannonEntropy, finitePushforwardWeights_average]

end InvariantIsing

end

end OAI
