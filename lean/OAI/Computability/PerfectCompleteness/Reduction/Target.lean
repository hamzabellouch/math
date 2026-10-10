import Std
import OAI.Computability.PerfectCompleteness.Model

namespace OAI

section

namespace PerfectCompleteness

theorem countSatisfied_le_length {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) (es : List (Edge l r q)) :
    countSatisfied a b es ≤ es.length := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    simp only [countSatisfied, List.length_cons]
    split <;> omega

theorem countSatisfied_eq_length_iff {l r q : Nat} (a : Fin l → Fin (2 * q))
    (b : Fin r → Fin q) (es : List (Edge l r q)) :
    countSatisfied a b es = es.length ↔ ∀ e ∈ es, e.satisfied a b = true := by
  induction es with
  | nil => simp [countSatisfied]
  | cons e es ih =>
    have bound := countSatisfied_le_length a b es
    cases h : e.satisfied a b <;> simp_all [countSatisfied, Nat.add_comm]
    omega

theorem Instance.edgeCount_positive {q : Nat} (G : Instance q) :
    0 < G.edges.length := by
  cases h : G.edges with
  | nil => exact False.elim (G.nonempty h)
  | cons e es => simp

def PerfectlyComplete {q : Nat} (G : Instance q) : Prop :=
  ∃ s : Labeling G, ∀ e ∈ G.edges, e.satisfied s.1 s.2 = true

structure RationalThreshold where
  numerator : Nat
  denominator : Nat
  positive : 0 < numerator
  belowOne : numerator < denominator

def SoundAt {q : Nat} (d : RationalThreshold) (G : Instance q) : Prop :=
  ∀ s : Labeling G,
    d.denominator * countSatisfied s.1 s.2 G.edges ≤ d.numerator * G.edges.length

end PerfectCompleteness

end

end OAI
