import Mathlib
import OAI.Computability.VertexCover.Analysis.GraphComplete
import OAI.Computability.VertexCover.Reduction.ReductionSound
import OAI.Computability.VertexCover.Reduction.DenseEncodingBound

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
namespace VertexCover.ClauseProjection
open UniqueGames
noncomputable section

def falseFormula : BinaryFormula.Formula :=
  ⟨[#v[⟨0,true⟩, ⟨0,true⟩, ⟨0,true⟩], #v[⟨0,false⟩, ⟨0,false⟩, ⟨0,false⟩]]⟩

theorem falseFormula_unsat : ¬falseFormula.Satisfiable := by
  rintro ⟨A, hA⟩
  have hpos := hA #v[⟨0,true⟩, ⟨0,true⟩, ⟨0,true⟩] (by simp [falseFormula])
  have hneg := hA #v[⟨0,false⟩, ⟨0,false⟩, ⟨0,false⟩] (by simp [falseFormula])
  cases h : A 0 <;> simp [BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, h] at hpos hneg

def inputFormula (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD falseFormula

def InputSAT (input : List Bool) : Prop :=
  ∃ F, BinaryEncoding.decodeFormula input = some F ∧ F.Satisfiable

theorem inputFormula_sat (input : List Bool) : (inputFormula input).Satisfiable ↔ InputSAT input := by
  unfold inputFormula InputSAT
  cases h : BinaryEncoding.decodeFormula input with
  | none => simp [falseFormula_unsat]
  | some F => simp

def binaryReduction (σ : ℝ) (hσ : 0 < σ) (input : List Bool) : VertexCover.LabelCover :=
  reduction σ hσ (BinaryFormula.dense (inputFormula input))

theorem binaryReduction_complete (σ : ℝ) (hσ : 0 < σ) (input : List Bool)
    (h : InputSAT input) :
    ∃ A : (binaryReduction σ hσ input).Labeling,
      ∀ e, (binaryReduction σ hσ input).Satisfies A e :=
  reduction_complete σ hσ _ (BinaryFormula.dense_completeness _ ((inputFormula_sat input).mpr h))

theorem binaryReduction_sound (σ : ℝ) (hσ : 0 < σ) (input : List Bool)
    (h : ¬InputSAT input) : (binaryReduction σ hσ input).value < σ := by
  apply reduction_sound
  intro hs
  exact h ((inputFormula_sat input).mp (BinaryFormula.dense_reflects _ hs))

end
end VertexCover.ClauseProjection

namespace VertexCover
noncomputable section

def rawGraph (m : ℕ) (hm : 4 ≤ m) (input : List Bool) : ExplicitGraph :=
  (ClauseProjection.binaryReduction (Parameters.σ m)
    (Parameters.σ_between m hm).1 input).explicitGraph m

theorem rawGraph_completeness (m : ℕ) (hm : 4 ≤ m) (input : List Bool)
    (h : ThreeSAT input) :
    ((rawGraph m hm input).coverNumber : ℝ) <
      ((1:ℝ)/2+1/(m:ℝ)) * (rawGraph m hm input).n := by
  have hc := ClauseProjection.binaryReduction_complete (Parameters.σ m)
    (Parameters.σ_between m hm).1 input h
  obtain ⟨A, hA⟩ := hc
  exact LabelCover.explicitGraph_complete _ m hm A hA

theorem rawLabelCover_soundness (m : ℕ) (hm : 4 ≤ m) (input : List Bool)
    (h : ¬ ThreeSAT input) :
    (ClauseProjection.binaryReduction (Parameters.σ m)
      (Parameters.σ_between m hm).1 input).value < Parameters.σ m :=
  ClauseProjection.binaryReduction_sound _ _ input h

end
end VertexCover


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
