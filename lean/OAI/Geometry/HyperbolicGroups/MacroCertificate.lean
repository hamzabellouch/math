import Mathlib
import OAI.Geometry.HyperbolicGroups.MetricHexagon

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- The literal 15-vertex macro graph: point and line vertices, and the single
subdivision vertex of the exceptional incidence D--CD. -/
abbrev Vertex := (Fin 7 ⊕ Fin 7) ⊕ Unit

def point (i : Fin 7) : Vertex := .inl (.inl i)
def line (l : Fin 7) : Vertex := .inl (.inr l)
def exceptional : Vertex := .inr ()

def Adjacent : Vertex → Vertex → Prop
  | .inl (.inl i), .inl (.inr l) => Incident i l ∧ (i,l) ≠ (3,4)
  | .inl (.inr l), .inl (.inl i) => Incident i l ∧ (i,l) ≠ (3,4)
  | .inl (.inl i), .inr _ => i = 3
  | .inr _, .inl (.inl i) => i = 3
  | .inl (.inr l), .inr _ => l = 4
  | .inr _, .inl (.inr l) => l = 4
  | _, _ => False
instance (a b : Vertex) : Decidable (Adjacent a b) := by
  rcases a with ((i|l)|⟨⟩) <;> rcases b with ((j|m)|⟨⟩) <;> unfold Adjacent <;> infer_instance

lemma adjacent_symm {a b : Vertex} (h : Adjacent a b) : Adjacent b a := by
  rcases a with ((i|l)|⟨⟩) <;> rcases b with ((j|m)|⟨⟩) <;> exact h

lemma adjacent_ne {a b : Vertex} (h : Adjacent a b) : a ≠ b := by
  rintro rfl
  rcases a with ((i|l)|⟨⟩) <;> exact h

/-- Keep at most the specified two points, but retain every line and the
subdivision vertex. Such an induced graph is a forest. -/
def Allowed (p q : Fin 7) : Vertex → Prop
  | .inl (.inl i) => i = p ∨ i = q
  | _ => True
instance (p q : Fin 7) (a : Vertex) : Decidable (Allowed p q a) := by
  rcases a with ((i|l)|⟨⟩) <;> unfold Allowed <;> infer_instance

/-- A leaf-elimination certificate, rooted at p. Ranks strictly rise towards
the unique common line and the root; the exceptional rank subdivides its edge.
This is a formula on the actual seven Fano vectors, not a graph hypothesis. -/
def rank (p q : Fin 7) : Vertex → ℕ
  | .inl (.inl i) => if i = p then 8 else if i = q then 4 else 0
  | .inl (.inr l) => if p ≠ q ∧ Incident p l ∧ Incident q l then 6 else 2
  | .inr _ => if (3:Fin 7) = p ∨ (3:Fin 7) = q then
      if p ≠ q ∧ Incident p 4 ∧ Incident q 4 then if p = 3 then 7 else 5 else 3
    else 1

def Certificate (p q : Fin 7) : Prop :=
  ∀ v a b : Vertex, (Allowed p q v ∧ Allowed p q a ∧ Allowed p q b ∧
    Adjacent v a ∧ Adjacent v b ∧ rank p q v ≤ rank p q a ∧ rank p q v ≤ rank p q b) → a = b
instance (p q : Fin 7) : Decidable (Certificate p q) := by
  unfold Certificate
  infer_instance

private lemma certificate_0_0 : Certificate 0 0 := by decide
private lemma certificate_0_1 : Certificate 0 1 := by decide
private lemma certificate_0_2 : Certificate 0 2 := by decide
private lemma certificate_0_3 : Certificate 0 3 := by decide
private lemma certificate_0_4 : Certificate 0 4 := by decide
private lemma certificate_0_5 : Certificate 0 5 := by decide
private lemma certificate_0_6 : Certificate 0 6 := by decide
private lemma certificate_1_0 : Certificate 1 0 := by decide
private lemma certificate_1_1 : Certificate 1 1 := by decide
private lemma certificate_1_2 : Certificate 1 2 := by decide
private lemma certificate_1_3 : Certificate 1 3 := by decide
private lemma certificate_1_4 : Certificate 1 4 := by decide
private lemma certificate_1_5 : Certificate 1 5 := by decide
private lemma certificate_1_6 : Certificate 1 6 := by decide
private lemma certificate_2_0 : Certificate 2 0 := by decide
private lemma certificate_2_1 : Certificate 2 1 := by decide
private lemma certificate_2_2 : Certificate 2 2 := by decide
private lemma certificate_2_3 : Certificate 2 3 := by decide
private lemma certificate_2_4 : Certificate 2 4 := by decide
private lemma certificate_2_5 : Certificate 2 5 := by decide
private lemma certificate_2_6 : Certificate 2 6 := by decide
private lemma certificate_3_0 : Certificate 3 0 := by decide
private lemma certificate_3_1 : Certificate 3 1 := by decide
private lemma certificate_3_2 : Certificate 3 2 := by decide
private lemma certificate_3_3 : Certificate 3 3 := by decide
private lemma certificate_3_4 : Certificate 3 4 := by decide
private lemma certificate_3_5 : Certificate 3 5 := by decide
private lemma certificate_3_6 : Certificate 3 6 := by decide
private lemma certificate_4_0 : Certificate 4 0 := by decide
private lemma certificate_4_1 : Certificate 4 1 := by decide
private lemma certificate_4_2 : Certificate 4 2 := by decide
private lemma certificate_4_3 : Certificate 4 3 := by decide
private lemma certificate_4_4 : Certificate 4 4 := by decide
private lemma certificate_4_5 : Certificate 4 5 := by decide
private lemma certificate_4_6 : Certificate 4 6 := by decide
private lemma certificate_5_0 : Certificate 5 0 := by decide
private lemma certificate_5_1 : Certificate 5 1 := by decide
private lemma certificate_5_2 : Certificate 5 2 := by decide
private lemma certificate_5_3 : Certificate 5 3 := by decide
private lemma certificate_5_4 : Certificate 5 4 := by decide
private lemma certificate_5_5 : Certificate 5 5 := by decide
private lemma certificate_5_6 : Certificate 5 6 := by decide
private lemma certificate_6_0 : Certificate 6 0 := by decide
private lemma certificate_6_1 : Certificate 6 1 := by decide
private lemma certificate_6_2 : Certificate 6 2 := by decide
private lemma certificate_6_3 : Certificate 6 3 := by decide
private lemma certificate_6_4 : Certificate 6 4 := by decide
private lemma certificate_6_5 : Certificate 6 5 := by decide
private lemma certificate_6_6 : Certificate 6 6 := by decide

lemma certificate (p q : Fin 7) : Certificate p q := by
  fin_cases p <;> fin_cases q
  · exact certificate_0_0
  · exact certificate_0_1
  · exact certificate_0_2
  · exact certificate_0_3
  · exact certificate_0_4
  · exact certificate_0_5
  · exact certificate_0_6
  · exact certificate_1_0
  · exact certificate_1_1
  · exact certificate_1_2
  · exact certificate_1_3
  · exact certificate_1_4
  · exact certificate_1_5
  · exact certificate_1_6
  · exact certificate_2_0
  · exact certificate_2_1
  · exact certificate_2_2
  · exact certificate_2_3
  · exact certificate_2_4
  · exact certificate_2_5
  · exact certificate_2_6
  · exact certificate_3_0
  · exact certificate_3_1
  · exact certificate_3_2
  · exact certificate_3_3
  · exact certificate_3_4
  · exact certificate_3_5
  · exact certificate_3_6
  · exact certificate_4_0
  · exact certificate_4_1
  · exact certificate_4_2
  · exact certificate_4_3
  · exact certificate_4_4
  · exact certificate_4_5
  · exact certificate_4_6
  · exact certificate_5_0
  · exact certificate_5_1
  · exact certificate_5_2
  · exact certificate_5_3
  · exact certificate_5_4
  · exact certificate_5_5
  · exact certificate_5_6
  · exact certificate_6_0
  · exact certificate_6_1
  · exact certificate_6_2
  · exact certificate_6_3
  · exact certificate_6_4
  · exact certificate_6_5
  · exact certificate_6_6


end HyperbolicObstruction.MacroGraph
end
end

section

end
end

end OAI
