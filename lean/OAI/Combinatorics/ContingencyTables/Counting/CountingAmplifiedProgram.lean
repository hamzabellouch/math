import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectProgram
import OAI.Combinatorics.ContingencyTables.Machines.RepeatedFractionProgram

namespace OAI

/-! # Outer confidence repetition of the executed counting program -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped CommonBasesFPRAS GridBoundary
abbrev Request := CountingDirectProgram.Request
abbrev Input := CountingDirectProgram.Input

variable (single : Input→TreeFraction.Fraction) (F : Realizer single)
variable (width : Request→ℕ) (N : Realizer width)

def repeats (req : Request) : ℕ := FractionRepetitionProgram.count req.2
def repeatsRealizer : Realizer repeats :=
  composition (f := fun req : Request => req.2) (g := FractionRepetitionProgram.count)
    second FractionRepetitionProgram.countRealizer
lemma polynomial_repeats : PolynomialTime repeatsRealizer :=
  polynomial_composition polynomial_second FractionRepetitionProgram.polynomial_count

def prepared (z : Input) : RepeatedFractionProgram.Input Request :=
  ((z.1,(repeats z.1,width z.1)),z.2)
def preparedRealizer : Realizer (prepared width) :=
  pair (pair first (pair (composition (f := fun z : Input => z.1) (g := repeats)
    first repeatsRealizer) (composition (f := fun z : Input => z.1) (g := width) first N))) second
lemma polynomial_prepared (hN : PolynomialTime N) : PolynomialTime (preparedRealizer width N) :=
  polynomial_pair (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_first polynomial_repeats)
    (polynomial_composition polynomial_first hN))) polynomial_second

attribute [local irreducible] prepared

def output (z : Input) : TreeFraction.Fraction := RepeatedFractionProgram.output single (prepared width z)
def outputRealizer : Realizer (output single width) :=
  composition (f := prepared width) (g := RepeatedFractionProgram.output single)
    (preparedRealizer width N) (RepeatedFractionProgram.outputRealizer F)
lemma polynomial_output (hF : PolynomialTime F) (hN : PolynomialTime N) :
    PolynomialTime (outputRealizer single F width N) :=
  polynomial_composition (polynomial_prepared width N hN) (RepeatedFractionProgram.polynomial_output F hF)

def budget (req : Request) : ℕ := repeats req*width req
def budgetRealizer : Realizer (budget width) :=
  composition (f := fun req : Request => (repeats req,width req))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair repeatsRealizer N) multiply
lemma polynomial_budget (hN : PolynomialTime N) : PolynomialTime (budgetRealizer width N) :=
  polynomial_composition (polynomial_pair polynomial_repeats hN) polynomial_multiply

lemma output_ofFn (req : Request) (hw : 0 < width req)
    (bits : Fin (budget width req)→Bool) :
    TreeFraction.val (output single width (req,List.ofFn bits))=
      rationalMedian (List.ofFn (fun i : Fin (repeats req) =>
        TreeFraction.val (single (req,List.ofFn (gridWordEquiv (repeats req) (width req) bits i))))) := by
  unfold output prepared
  exact RepeatedFractionProgram.output_ofFn (f := single) req (repeats req) (width req) hw bits

end ContingencyTables.CountingAmplifiedProgram

end OAI
