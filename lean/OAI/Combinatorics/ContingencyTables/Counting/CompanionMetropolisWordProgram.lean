import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram

namespace OAI

/-! # Bounded slicing of one flat companion transition word -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

/-- The fixed frame, the acceptance precision, current code, and fresh word. -/
abbrev Input := ((CompanionMetropolisProgram.Frame × ℕ) × List ℕ) × List Bool

def proposalWidth (z : Input) : ℕ := Nat.clog 2 ((z.1.2.length/2)^2)
def proposalWidthRealizer : Realizer proposalWidth := by
  let p : Realizer (fun z : Input => z.1.2.length/2) :=
    composition (f := fun z : Input => (z.1.2.length,2))
      (g := fun ab : ℕ × ℕ => ab.1/ab.2)
      (pair (composition (composition first second) listLength) (constant 2)) quotient
  exact composition (f := fun z : Input => (z.1.2.length/2)^2) (g := Nat.clog 2)
    ((composition (pair p p) multiply).congr (fun z => (pow_two _).symm)) ceilLogTwoRealizer
lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  unfold proposalWidthRealizer
  apply polynomial_composition _ polynomial_ceilLogTwo
  apply polynomial_congr
  apply polynomial_composition _ polynomial_multiply
  apply polynomial_pair
  all_goals exact (polynomial_composition
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) (polynomial_constant 2)) polynomial_quotient)

def context (z : Input) : RootedEstimatorLayoutProgram.Context := z.1.1.1.1.1.1
def contextRealizer : Realizer context :=
  composition (composition (composition (composition (composition first first) first) first) first) first
lemma polynomial_context : PolynomialTime contextRealizer := by
  unfold contextRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_first) polynomial_first) polynomial_first

def queryWidth (z : Input) : ℕ := z.1.1.1.1.1.2*RootedEstimatorLayoutProgram.wordWidth (context z)
def queryWidthRealizer : Realizer queryWidth :=
  composition (f := fun z : Input =>
    (z.1.1.1.1.1.2,RootedEstimatorLayoutProgram.wordWidth (context z)))
    (g := fun ab : ℕ × ℕ => ab.1*ab.2)
    (pair (composition (composition (composition (composition (composition first first) first) first) first) second)
      (composition (f := context) (g := RootedEstimatorLayoutProgram.wordWidth)
        contextRealizer RootedEstimatorLayoutProgram.wordWidthRealizer)) multiply
lemma polynomial_queryWidth : PolynomialTime queryWidthRealizer :=
  polynomial_composition (polynomial_pair (by tree_poly)
    (polynomial_composition polynomial_context RootedEstimatorLayoutProgram.polynomial_wordWidth)) polynomial_multiply

attribute [local irreducible] context queryWidth proposalWidth

/-- Offsets are computed in binary; the physical `take`/`drop` calls remain
bounded by the supplied word on every malformed input. -/
def firstOffset (z : Input) : ℕ := 1+proposalWidth z
def firstOffsetRealizer : Realizer firstOffset :=
  composition (f := fun z : Input => (1,proposalWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair (constant 1) proposalWidthRealizer) TreeTyped.add
lemma polynomial_firstOffset : PolynomialTime firstOffsetRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 1) polynomial_proposalWidth) polynomial_add

def secondOffset (z : Input) : ℕ := firstOffset z+queryWidth z
attribute [local irreducible] firstOffset

def secondOffsetRealizer : Realizer secondOffset :=
  composition (f := fun z : Input => (firstOffset z,queryWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair firstOffsetRealizer queryWidthRealizer) TreeTyped.add
lemma polynomial_secondOffset : PolynomialTime secondOffsetRealizer :=
  polynomial_composition (polynomial_pair polynomial_firstOffset polynomial_queryWidth) polynomial_add

def coinOffset (z : Input) : ℕ := secondOffset z+queryWidth z
attribute [local irreducible] secondOffset

def coinOffsetRealizer : Realizer coinOffset :=
  composition (f := fun z : Input => (secondOffset z,queryWidth z)) (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair secondOffsetRealizer queryWidthRealizer) TreeTyped.add
lemma polynomial_coinOffset : PolynomialTime coinOffsetRealizer :=
  polynomial_composition (polynomial_pair polynomial_secondOffset polynomial_queryWidth) polynomial_add

private def slice (start count : Input → ℕ) (z : Input) : List Bool :=
  (z.2.drop (start z)).take (count z)
private def sliceRealizer {start count : Input → ℕ}
    (S : Realizer start) (C : Realizer count) : Realizer (slice start count) :=
  composition (pair (composition (pair second S) dropFast) C) takeFast
private lemma polynomial_slice {start count : Input → ℕ}
    (S : Realizer start) (C : Realizer count) (hS : PolynomialTime S) (hC : PolynomialTime C) :
    PolynomialTime (sliceRealizer S C) :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_second hS) polynomial_dropFast) hC) polynomial_takeFast

def fields (z : Input) : CompanionMetropolisProgram.Words :=
  (z.2.getD 0 false,
    (slice (fun _ => 1) proposalWidth z,
      ((slice firstOffset queryWidth z,slice secondOffset queryWidth z),
        slice coinOffset (fun z => z.1.1.2) z)))
def fieldsRealizer : Realizer fields :=
  pair (composition (pair second (constant 0)) (getDFast false))
    (pair (sliceRealizer (constant 1) proposalWidthRealizer)
      (pair (pair (sliceRealizer firstOffsetRealizer queryWidthRealizer)
        (sliceRealizer secondOffsetRealizer queryWidthRealizer))
        (sliceRealizer coinOffsetRealizer (composition (composition first first) second))))
lemma polynomial_fields : PolynomialTime fieldsRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
    (polynomial_getDFast false))
    (polynomial_pair (polynomial_slice _ _ (polynomial_constant 1) polynomial_proposalWidth)
      (polynomial_pair (polynomial_pair
        (polynomial_slice _ _ polynomial_firstOffset polynomial_queryWidth)
        (polynomial_slice _ _ polynomial_secondOffset polynomial_queryWidth))
        (polynomial_slice _ _ polynomial_coinOffset (by tree_poly))))

def stepInput (z : Input) : CompanionMetropolisProgram.Input := ((z.1.1.1,z.1.2),fields z)
def stepInputRealizer : Realizer stepInput :=
  pair (pair (composition (composition first first) first) (composition first second)) fieldsRealizer
lemma polynomial_stepInput : PolynomialTime stepInputRealizer :=
  polynomial_pair (polynomial_pair (by tree_poly) (polynomial_composition polynomial_first polynomial_second))
    polynomial_fields

attribute [local irreducible] stepInput

def output (z : Input) : List ℕ := CompanionMetropolisProgram.output (stepInput z)
def outputRealizer : Realizer output :=
  composition (f := stepInput) (g := CompanionMetropolisProgram.output)
    stepInputRealizer CompanionMetropolisProgram.outputRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_stepInput CompanionMetropolisProgram.polynomial_output

end ContingencyTables.CompanionMetropolisWordProgram

end OAI
