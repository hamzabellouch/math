import OAI.Combinatorics.ContingencyTables.Rooted.RootedEstimatorWordLaw
import OAI.Combinatorics.ContingencyTables.Machines.MedianFractionProgram

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

abbrev Input := (Context×ℕ)×((List Bool×List Bool)×List Bool)

def words (z : Input) : List (List Bool) :=
  (wordChunks (wordWidth z.1.1,z.2.2)).take z.1.2
def wordsRealizer : Realizer words := by
  let chunks : Realizer (fun z : Input => wordChunks (wordWidth z.1.1,z.2.2)) :=
    composition (f := fun z : Input => (wordWidth z.1.1,z.2.2)) (g := wordChunks)
      (pair (composition (f := fun z : Input => z.1.1) (g := wordWidth)
        (composition first first) wordWidthRealizer) (composition second second)) wordChunksRealizer
  exact composition (f := fun z : Input => (wordChunks (wordWidth z.1.1,z.2.2),z.1.2))
    (g := fun p : List (List Bool)×ℕ => p.1.take p.2)
    (pair chunks (composition first second)) takeFast
lemma polynomial_words : PolynomialTime wordsRealizer := by
  unfold wordsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_wordWidth) (polynomial_composition polynomial_second polynomial_second))
      polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_takeFast

def sample (z : Input×List Bool) : TreeFraction.Fraction :=
  RootedEstimatorWordProgram.output (z.1.1.1,(z.1.2.1,z.2))
def sampleRealizer : Realizer sample :=
  composition (f := fun z : Input×List Bool => (z.1.1.1,(z.1.2.1,z.2)))
    (g := RootedEstimatorWordProgram.output)
    (pair (composition (composition first first) first)
      (pair (composition (composition first second) first) second))
    RootedEstimatorWordProgram.outputRealizer
lemma polynomial_sample : PolynomialTime sampleRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_second)) RootedEstimatorWordProgram.polynomial_output

def samples (z : Input) : List TreeFraction.Fraction := (words z).map (fun bits => sample (z,bits))
def samplesRealizer : Realizer samples :=
  composition (pair identity wordsRealizer) (mapWith sampleRealizer)
lemma polynomial_samples : PolynomialTime samplesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_words)
    (polynomial_mapWith polynomial_sample)

attribute [local irreducible] samples

def output (z : Input) : TreeFraction.Fraction := MedianFractionProgram.median (samples z)
def outputRealizer : Realizer output :=
  composition (f := samples) (g := MedianFractionProgram.median)
    samplesRealizer MedianFractionProgram.medianRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_samples MedianFractionProgram.polynomial_median

open GridBoundary CommonBasesFPRAS
open scoped Classical

theorem output_ofFn (c : Context) (R : ℕ) (hw : 0 < wordWidth c)
    (markers : List Bool×List Bool) (bits : Fin (R*wordWidth c) → Bool) :
    TreeFraction.val (output ((c,R),(markers,List.ofFn bits)))=
      rationalMedian (List.ofFn (fun i : Fin R => TreeFraction.val
        (RootedEstimatorWordProgram.output (RootedEstimatorWordProgram.input c markers
          (gridWordEquiv R (wordWidth c) bits i))))) := by
  rw [output,MedianFractionProgram.median_val]
  have hwords : words ((c,R),(markers,List.ofFn bits))=
      List.ofFn (fun i : Fin R => List.ofFn (gridWordEquiv R (wordWidth c) bits i)) := by
    change (wordChunks (wordWidth c,List.ofFn bits)).take R=_
    rw [wordChunks_ofFn hw]
    exact List.take_of_length_le (by simp)
  unfold samples
  rw [hwords]
  simp only [List.map_ofFn]
  rfl

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
