import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectSemantics

namespace OAI

/-! # The public counting dispatch preserves the original bounded input -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CompanionFactorialApplication
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parsedInput_public (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (bits : List Bool) :
    parsedInput (Algorithms.encodeCountingInput r c b epsilon delta,bits)=
      (CountingDirectProgram.request r c b epsilon delta,bits) := by
  unfold parsedInput
  rw [CountingInputParser.public_spec]
  rfl

lemma feasible_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    feasible (CountingDirectProgram.request r c b epsilon delta)=true ↔
      ∃ X,TableTightening.Feasible r c b X := by
  exact NetworkFeasibilityProgram.test_correct hEK r c b

lemma count_zero_iff_rejected (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    Algorithms.count r c b=0 ↔ feasible (CountingDirectProgram.request r c b epsilon delta)=false := by
  constructor
  · intro hz
    apply Bool.eq_false_iff.mpr
    intro hf
    obtain ⟨X,hX⟩ := (feasible_data hEK r c b epsilon delta).mp hf
    have hp : 0 < Fintype.card (BoundedTable r c b) :=
      Fintype.card_pos_iff.mpr ⟨⟨⟨X,hX.1⟩,hX.2⟩⟩
    exact (Nat.ne_of_gt hp) hz
  · intro hf
    have hn : ¬∃ X,TableTightening.Feasible r c b X := by
      intro hx
      have ht := (feasible_data hEK r c b epsilon delta).mpr hx
      rw [hf] at ht
      exact Bool.false_ne_true ht
    have hEmpty : IsEmpty (BoundedTable r c b) := ⟨fun X => hn ⟨X.val.val,X.val.property,X.property⟩⟩
    let := hEmpty
    exact Fintype.card_eq_zero

lemma direct_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    direct (CountingDirectProgram.request r c b epsilon delta)=true ↔
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he))=0 := by
  unfold direct CountingDirectProgram.request
  rw [CountingComputedSettings.labelCount_data hEK r c b hne epsilon he]
  simp only [decide_eq_true_eq]

lemma output_rejected (positive : Input→TreeFraction.Fraction) (req : Request)
    (h : feasible req=false) (bits : List Bool) : output positive (req,bits)=(0,1) := by
  simp only [output,h,Bool.false_eq_true,ite_false]

lemma output_direct (positive : Input→TreeFraction.Fraction) (req : Request)
    (hf : feasible req=true) (hd : direct req=true) (bits : List Bool) :
    output positive (req,bits)=CountingDirectProgram.output (req,bits) := by
  simp only [output,feasibleOutput,hf,hd,ite_true]

lemma output_positive (positive : Input→TreeFraction.Fraction) (req : Request)
    (hf : feasible req=true) (hd : direct req=false) (bits : List Bool) :
    output positive (req,bits)=positive (req,bits) := by
  simp only [output,feasibleOutput,hf,hd,ite_true,Bool.false_eq_true,ite_false]

lemma budget_rejected (positive : Request→ℕ) (req : Request)
    (h : feasible req=false) : budget positive req=0 := by
  simp only [budget,h,Bool.false_eq_true,ite_false]

lemma budget_direct (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=true) :
    budget positive req=CountingDirectProgram.budget req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true]

lemma budget_positive (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=false) : budget positive req=positive req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true,Bool.false_eq_true,ite_false]

end
end ContingencyTables.CountingBranchProgram

end OAI
