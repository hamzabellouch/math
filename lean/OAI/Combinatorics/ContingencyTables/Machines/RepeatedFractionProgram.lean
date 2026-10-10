import OAI.Combinatorics.ContingencyTables.Machines.MedianFractionProgram
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseMetropolisSemantics

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type} [Codec X]
abbrev Input (X : Type) := (X×(ℕ×ℕ))×List Bool

def words (z : Input X) : List (List Bool) :=
  (wordChunks (z.1.2.2,z.2)).take z.1.2.1
def wordsRealizer : Realizer (words (X:=X)) :=
  composition (f := fun z : Input X => (wordChunks (z.1.2.2,z.2),z.1.2.1))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair
      (composition (f := fun z : Input X => (z.1.2.2,z.2)) (g := wordChunks)
        (pair (composition (composition first second) second) second) wordChunksRealizer)
      (composition (composition first second) first)) takeFast
lemma polynomial_words : PolynomialTime (wordsRealizer (X:=X)) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_second) polynomial_wordChunks)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
    polynomial_takeFast

variable {f : X×List Bool→TreeFraction.Fraction}

def sample (f : X×List Bool→TreeFraction.Fraction) (z : Input X×List Bool) : TreeFraction.Fraction :=
  f (z.1.1.1,z.2)
def sampleRealizer (F : Realizer f) : Realizer (sample f) :=
  composition (f := fun z : Input X×List Bool => (z.1.1.1,z.2)) (g := f)
    (pair (composition (composition first first) first) second) F
lemma polynomial_sample (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (sampleRealizer F) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) hF

def samples (f : X×List Bool→TreeFraction.Fraction) (z : Input X) : List TreeFraction.Fraction :=
  (words z).map (fun bits => sample f (z,bits))
def samplesRealizer (F : Realizer f) : Realizer (samples f) :=
  composition (pair identity wordsRealizer) (mapWith (sampleRealizer F))
lemma polynomial_samples (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (samplesRealizer F) :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_words)
    (polynomial_mapWith (polynomial_sample F hF))

attribute [local irreducible] samples

def output (f : X×List Bool→TreeFraction.Fraction) (z : Input X) : TreeFraction.Fraction :=
  MedianFractionProgram.median (samples f z)
def outputRealizer (F : Realizer f) : Realizer (output f) :=
  composition (f := samples f) (g := MedianFractionProgram.median)
    (samplesRealizer F) MedianFractionProgram.medianRealizer
lemma polynomial_output (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (outputRealizer F) :=
  polynomial_composition (polynomial_samples F hF) MedianFractionProgram.polynomial_median

open GridBoundary CommonBasesFPRAS

omit [Codec X] in
theorem output_ofFn (x : X) (r w : ℕ) (hw : 0 < w) (bits : Fin (r*w)→Bool) :
    TreeFraction.val (output f ((x,(r,w)),List.ofFn bits))=
      rationalMedian (List.ofFn (fun i : Fin r =>
        TreeFraction.val (f (x,List.ofFn (gridWordEquiv r w bits i))))) := by
  rw [output,MedianFractionProgram.median_val]
  have hwords : words ((x,(r,w)),List.ofFn bits)=
      List.ofFn (fun i : Fin r => List.ofFn (gridWordEquiv r w bits i)) := by
    change (wordChunks (w,List.ofFn bits)).take r=_
    rw [wordChunks_ofFn hw]
    exact List.take_of_length_le (by simp)
  unfold samples
  rw [hwords]
  simp only [List.map_ofFn]
  rfl

end ContingencyTables.RepeatedFractionProgram

end OAI
