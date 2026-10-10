import Mathlib
import OAI.Computability.VertexCover.PCP.Overlay
import OAI.Computability.VertexCover.PCP.PoweringLazy

namespace OAI

                                                                                       

namespace UniqueGames.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a «c»
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a «c»

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

theorem complete (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, (constraintGraph G).edgeSatisfied labeling e = true := by
  rintro ⟨v,b,d⟩
  cases b with
  | false => rfl
  | true =>
    rw [edgeSatisfied_true G htail]
    exact h (v,d)

theorem complete_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (∀ e, (constraintGraph G).edgeSatisfied labeling e = true) ↔
      ∀ e, G.edgeSatisfied labeling e = true := by
  constructor
  · intro h
    rintro ⟨v,d⟩
    rw [← edgeSatisfied_true G htail]
    exact h (v,(true,d))
  · exact complete G htail labeling

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) :
    (constraintGraph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, (complete_iff G htail labeling).mp h⟩
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, complete G htail labeling h⟩

theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

theorem card_ports [Fintype D] :
    Fintype.card (Bool × D) = 2 * Fintype.card D := by
  simp

theorem card_darts [Fintype V] [Fintype D] :
    Fintype.card (V × (Bool × D)) = 2 * Fintype.card (V × D) := by
  simp [Fintype.card_prod, Nat.mul_left_comm]

theorem rejection_density_eq_half [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    ((constraintGraph G).rejectionCount labeling : ℝ) /
        (Fintype.card (V × (Bool × D)) : ℝ) =
      ((G.rejectionCount labeling : ℝ) / (Fintype.card (V × D) : ℝ)) / 2 := by
  rw [rejectionCount_eq G htail, card_darts]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
  ring

end UniqueGames.Foundations.PCP.LazyConstraint

end OAI
