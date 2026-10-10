import Mathlib
import OAI.Computability.VertexCover.PCP.ExpanderFamily
import OAI.Computability.VertexCover.PCP.GraphGap
import OAI.Computability.VertexCover.PCP.InitialGraph

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                    
section

noncomputable section

namespace UniqueGames.Foundations.PCP.FiniteGraph

structure Bundle (A : Type) where
  Vertex : Type
  Dart : Type
  vertexFintype : Fintype Vertex
  dartFintype : Fintype Dart
  vertexDecidableEq : DecidableEq Vertex
  dartDecidableEq : DecidableEq Dart
  dartNonempty : Nonempty Dart
  graph : ConstraintGraph Vertex Dart A

namespace Bundle

variable {A : Type}

instance instFintypeVertex (G : Bundle A) : Fintype G.Vertex := G.vertexFintype
instance instFintypeDart (G : Bundle A) : Fintype G.Dart := G.dartFintype
instance instDecidableEqVertex (G : Bundle A) : DecidableEq G.Vertex := G.vertexDecidableEq
instance instDecidableEqDart (G : Bundle A) : DecidableEq G.Dart := G.dartDecidableEq
instance instNonemptyDart (G : Bundle A) : Nonempty G.Dart := G.dartNonempty

instance instNonemptyVertex (G : Bundle A) : Nonempty G.Vertex := by
  obtain ⟨d⟩ := G.dartNonempty
  exact ⟨G.graph.tail d⟩

def ofGraph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) : Bundle A where
  Vertex := V
  Dart := E
  vertexFintype := inferInstance
  dartFintype := inferInstance
  vertexDecidableEq := inferInstance
  dartDecidableEq := inferInstance
  dartNonempty := inferInstance
  graph := G

def size (G : Bundle A) : Nat := Fintype.card G.Vertex + Fintype.card G.Dart

def Satisfiable (G : Bundle A) : Prop := G.graph.Satisfiable

def rejectionCount (G : Bundle A) (labeling : G.Vertex → A) : Nat :=
  G.graph.rejectionCount labeling

theorem size_positive (G : Bundle A) : 0 < G.size :=
  lt_of_lt_of_le (Fintype.card_pos : 0 < Fintype.card G.Dart) (Nat.le_add_left _ _)

theorem dartCard_le_size (G : Bundle A) : Fintype.card G.Dart ≤ G.size :=
  Nat.le_add_left _ _

@[simp] theorem ofGraph_graph {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).graph = G := rfl

@[simp] theorem ofGraph_size {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).size = Fintype.card V + Fintype.card E := rfl

@[simp] theorem ofGraph_satisfiable {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).Satisfiable ↔ G.Satisfiable := Iff.rfl

@[simp] theorem ofGraph_rejectionCount {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E]
    (G : ConstraintGraph V E A) (labeling : V → A) :
    (ofGraph G).rejectionCount labeling = G.rejectionCount labeling := rfl

section Gap

variable [Fintype A] [Nonempty A]

def minimumRejections (G : Bundle A) : Nat := G.graph.minimumRejections

def gap (G : Bundle A) : ℝ := G.graph.gap

theorem exists_minimizer (G : Bundle A) :
    ∃ labeling : G.Vertex → A, G.rejectionCount labeling = G.minimumRejections :=
  G.graph.exists_minimizer

theorem gap_nonnegative (G : Bundle A) : 0 ≤ G.gap := G.graph.gap_nonnegative

theorem gap_le_one (G : Bundle A) : G.gap ≤ 1 := G.graph.gap_le_one

theorem gap_eq_zero_iff (G : Bundle A) : G.gap = 0 ↔ G.Satisfiable :=
  G.graph.gap_eq_zero_iff

theorem le_gap_iff (G : Bundle A) (ε : ℝ) :
    ε ≤ G.gap ↔ ∀ labeling : G.Vertex → A,
      ε * Fintype.card G.Dart ≤ (G.rejectionCount labeling : ℝ) :=
  G.graph.le_gap_iff ε

theorem inverse_card_le_gap_of_unsatisfiable (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 / (Fintype.card G.Dart : ℝ) ≤ G.gap :=
  G.graph.inverse_card_le_gap_of_unsatisfiable unsat

theorem one_le_dartCard_mul_gap (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 ≤ (Fintype.card G.Dart : ℝ) * G.gap := by
  have he : (0 : ℝ) < Fintype.card G.Dart := by exact_mod_cast Fintype.card_pos
  have h := (div_le_iff₀ he).mp (G.inverse_card_le_gap_of_unsatisfiable unsat)
  simpa only [mul_comm] using h

theorem one_le_size_mul_gap (G : Bundle A) (unsat : ¬ G.Satisfiable) :
    1 ≤ (G.size : ℝ) * G.gap := by
  have hsize : (Fintype.card G.Dart : ℝ) ≤ (G.size : ℝ) := by
    exact_mod_cast G.dartCard_le_size
  exact (G.one_le_dartCard_mul_gap unsat).trans
    (mul_le_mul_of_nonneg_right hsize G.gap_nonnegative)

@[simp] theorem ofGraph_minimumRejections {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).minimumRejections = G.minimumRejections := rfl

@[simp] theorem ofGraph_gap {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [Nonempty E] (G : ConstraintGraph V E A) :
    (ofGraph G).gap = G.gap := rfl

end Gap

end Bundle

end UniqueGames.Foundations.PCP.FiniteGraph

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
