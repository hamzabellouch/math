import Mathlib
import OAI.Computability.VertexCover.Machines.SimpleLC
import OAI.Computability.VertexCover.Machines.PowerLC
import OAI.Computability.VertexCover.Machines.GraphOutput
import OAI.Computability.VertexCover.Machines.FinalCNFCorrect
import OAI.Computability.VertexCover.Machines.Approximation

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

namespace VertexCover.Machine.MainReduction
open UniqueGames UniqueGames.Foundations
open ClauseProjection
noncomputable section

def gapInput (F : Target.Formula) : SimpleLC.NEFormula :=
  ⟨PCP.TableIteration.gapMap fixedBaseTable F,
    PCP.TableIteration.gapMap_nonempty fixedBaseTable F⟩
def gapInputPoly : Poly FormulaParser.targetCode SimpleLC.code gapInput :=
  (FinalCNFMachine.gapPoly fixedBaseTable).encodeCongr id (fun _ => rfl) (fun _ => rfl)
def base (input : List Bool) : FixedLC 7 2 :=
  SimpleLC.output (gapInput (BinaryFormula.dense (inputFormula input)))
def basePoly : Poly id FixedLC.code base :=
  (((FormulaParser.inputFormulaPoly.comp FormulaParser.densePoly).comp gapInputPoly).comp
    SimpleLC.outputPoly).congr (fun _ => rfl)
theorem base_toLC (input : List Bool) :
    (base input).toLC=baseReduction (BinaryFormula.dense (inputFormula input)) := rfl

def repeated (σ : ℝ) (hσ : 0<σ) (input : List Bool) :
    FixedLC (7^repetitionLength σ hσ) (2^repetitionLength σ hσ) :=
  (base input).power (repetitionLength σ hσ)
def repeatedPoly (σ : ℝ) (hσ : 0<σ) :
    Poly id FixedLC.code (repeated σ hσ) :=
  basePoly.comp (FixedLC.powerPoly (by decide) (by decide) (repetitionLength σ hσ))
def repetitionIso (σ : ℝ) (hσ : 0<σ) (input : List Bool) :
    LabelCover.Iso (repeated σ hσ input).toLC (binaryReduction σ hσ input) :=
  LabelCover.numberIso (base input).toLC (repetitionLength σ hσ)
theorem repeated_complete (σ : ℝ) (hσ : 0<σ) (input : List Bool) (h : ThreeSAT input) :
    ∃ A : (repeated σ hσ input).toLC.Labeling,
      ∀ e, (repeated σ hσ input).toLC.Satisfies A e := by
  obtain ⟨A,hA⟩ := binaryReduction_complete σ hσ input h
  exact ⟨(repetitionIso σ hσ input).symm.labeling A,
    (repetitionIso σ hσ input).symm.perfect A hA⟩
theorem repeated_sound (σ : ℝ) (hσ : 0<σ) (input : List Bool) (h : ¬ThreeSAT input) :
    (repeated σ hσ input).toLC.value < σ := by
  rw [(repetitionIso σ hσ input).value_eq]
  exact binaryReduction_sound σ hσ input h

def construct (m : ℕ) (hm : 4 ≤ m) (input : List Bool) : ExplicitGraph :=
  GraphMachine.explicitGraph (repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input)
    (Parameters.d m) (Parameters.t m)
def constructPoly (m : ℕ) (hm : 4 ≤ m) : Poly id ExplicitGraph.bits (construct m hm) :=
  (repeatedPoly (Parameters.σ m) (Parameters.σ_between m hm).1).comp
    (GraphMachine.outputPoly (pow_pos (by decide) _) (pow_pos (by decide) _)
      (Parameters.d m) (Parameters.t m))
theorem construct_complete (m : ℕ) (hm : 4 ≤ m) (input : List Bool) (h : ThreeSAT input) :
    ((construct m hm input).coverNumber:ℝ) <
      (1/2+1/(m:ℝ))*(construct m hm input).n := by
  let I := repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input
  obtain ⟨A,hA⟩ := repeated_complete (Parameters.σ m) (Parameters.σ_between m hm).1 input h
  obtain ⟨C,hC,hcard⟩ := I.toLC.graph_completeness_cover m hm A hA
  exact ExplicitGraph.numbered_complete _ (GraphMachine.fullEquiv I (Parameters.d m)) C hC _ hcard
theorem construct_sound (m : ℕ) (hm : 4 ≤ m) (input : List Bool) (h : ¬ThreeSAT input) :
    (1-1/(m:ℝ))*(construct m hm input).n < ((construct m hm input).coverNumber:ℝ) := by
  let I := repeated (Parameters.σ m) (Parameters.σ_between m hm).1 input
  have hv := repeated_sound (Parameters.σ m) (Parameters.σ_between m hm).1 input h
  exact ExplicitGraph.numbered_sound _ (GraphMachine.fullEquiv I (Parameters.d m)) _
    (I.toLC.graph_soundness_cover m hm hv.le)

def reduction (m : ℕ) (hm : 4 ≤ m) : GapReduction m where
  construct := construct m hm
  computation := (constructPoly m hm).computation
  finiteAlphabet := (constructPoly m hm).finiteAlphabet
  completeness := construct_complete m hm
  soundness := construct_sound m hm
end
end VertexCover.Machine.MainReduction

namespace VertexCover
 theorem explicit_cover_gap (m : ℕ) (hm : 4 ≤ m) : Nonempty (GapReduction m) :=
  ⟨Machine.MainReduction.reduction m hm⟩
 theorem every_fixed_factor_below_two (α : ℝ) (hα : 1 ≤ α) (hα2 : α < 2)
    (algorithm : Approximation α) : Nonempty ThreeSATDecision := by
  obtain ⟨m,hm,hsep⟩ := exists_separating_integer hα2
  exact ⟨decisionOfGap hα m hm hsep (Machine.MainReduction.reduction m hm) algorithm⟩
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
