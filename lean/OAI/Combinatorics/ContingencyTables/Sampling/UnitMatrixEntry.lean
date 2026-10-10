import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixProgram
import OAI.Combinatorics.ContingencyTables.Sampling.UnitFiniteLaw

namespace OAI

/-! # Integer transition entries for the all-small walk -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

abbrev WordInput := MatrixEntryInput×List Bool

def wordViews (z : WordInput) : List ℕ×List ℕ :=
  (codeNeighborProposal (sourceData z.1,z.2)).getD z.1.2.1

def wordViewsRealizer : Realizer wordViews :=
  composition (pair (composition (composition first second) first)
    (composition (pair (composition first sourceDataRealizer) second) codeNeighborProposalRealizer))
    FirstSuccessProgram.defaultRealizer

lemma polynomial_wordViews : PolynomialTime wordViewsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_sourceData) polynomial_second)
      polynomial_codeNeighborProposal)) FirstSuccessProgram.polynomial_default

def wordCount (z : WordInput) : ℕ := if wordViews z=z.1.2.2 then 1 else 0

def wordCountRealizer : Realizer wordCount :=
  (choose (composition (pair wordViewsRealizer
    (composition (composition first second) second)) profileCodeEqual)
    (constant 1) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq]
      rfl)

lemma polynomial_wordCount : PolynomialTime wordCountRealizer := by
  unfold wordCountRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition (polynomial_pair polynomial_wordViews
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_profileCodeEqual) (polynomial_constant 1) (polynomial_constant 0)

def validEntry (z : MatrixEntryInput) : ℕ :=
  ((booleanWords z.1.2).map (fun w => wordCount (z,w))).sum

def entryWords (z : MatrixEntryInput) : MatrixEntryInput×List (List Bool) :=
  (z,booleanWords z.1.2)

def entryWordsRealizer : Realizer entryWords :=
  pair identity (composition (f := fun z : MatrixEntryInput => z.1.2)
    (g := booleanWords) (composition first second) booleanWordsRealizer)

def wordSum (z : MatrixEntryInput×List (List Bool)) : ℕ :=
  (z.2.map (fun w => wordCount (z.1,w))).sum

def wordSumRealizer : Realizer wordSum := composition (mapWith wordCountRealizer) listSum

lemma polynomial_wordSum : PolynomialTime wordSumRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_wordCount) polynomial_listSum

def validEntryRealizer : Realizer validEntry :=
  composition (f := entryWords) (g := wordSum) entryWordsRealizer wordSumRealizer

attribute [local irreducible] wordCount wordViews wordCountRealizer wordViewsRealizer

def entryMeasure (z : MatrixEntryInput) : ℕ := gridStateCount (z.1.2,2)+weight z

lemma work_entryWords : WorkBound entryWordsRealizer entryMeasure := by
  have hi (z : MatrixEntryInput) : weight z ≤ X.eval (entryMeasure z) := by
    simp only [Polynomial.eval_X,entryMeasure]
    omega
  have hw : WorkBound (composition (f := fun z : MatrixEntryInput => z.1.2)
      (g := booleanWords) (composition first second) booleanWordsRealizer) entryMeasure := by
    apply work_composition (work_of_polynomial
      (polynomial_composition polynomial_first polynomial_second) X hi) work_booleanWords X
    intro z
    have hh : weight z.1.2 ≤ weight z := (weight_snd z.1).trans (weight_fst z)
    simp only [Polynomial.eval_X,entryMeasure,Function.comp_apply]
    omega
  unfold entryWordsRealizer
  exact work_pair (work_of_polynomial polynomial_identity X hi) hw X hi

lemma work_validEntry : WorkBound validEntryRealizer entryMeasure := by
  obtain ⟨p,hp⟩ := work_entryWords
  obtain ⟨q,hq⟩ := polynomial_wordSum
  refine ⟨p+q.comp p,fun z => ?_⟩
  have h1 := hp z
  have h2 := hq (entryWords z)
  have h3 := polynomial_eval_monotone q ((Nat.le_add_left _ _).trans h1)
  dsimp only at h3
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  unfold validEntryRealizer validEntry
  change entryWordsRealizer.cost z+wordSumRealizer.cost (entryWords z)+
    weight (wordSum (entryWords z))≤_
  omega

def denominator (z : MatrixParameters) : ℕ := BinaryPowerPrograms.power (2,z.2.length)

def denominatorRealizer : Realizer denominator :=
  composition (pair (constant 2) (composition second listLength)) BinaryPowerPrograms.powerRealizer

lemma work_denominator : WorkBound denominatorRealizer (fun z => weight z) := by
  unfold denominatorRealizer
  apply work_composition (work_of_polynomial (polynomial_pair (polynomial_constant 2)
    (polynomial_composition polynomial_second polynomial_listLength)) X (fun _ => by simp))
    BinaryPowerPrograms.work_power (X+9)
  intro z
  change z.2.length+weight (2:ℕ) ≤ (X+9).eval (weight z)
  have htwo : weight (2:ℕ) ≤ 9 := by simpa using weight_nat_numeric 2
  have hl := (list_length_le_weight z.2).trans (weight_snd z)
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

def diagonalEntry (z : MatrixEntryInput) : ℕ :=
  if z.2.1=z.2.2 then denominator z.1 else 0

def diagonalEntryRealizer : Realizer diagonalEntry :=
  (choose (composition second profileCodeEqual) (composition first denominatorRealizer)
    (constant 0)).congr (by intro z; simp only [Function.comp_apply,decide_eq_true_eq]; rfl)

lemma work_diagonalEntry : WorkBound diagonalEntryRealizer entryMeasure := by
  have hi (z : MatrixEntryInput) : weight z ≤ X.eval (entryMeasure z) := by
    simp only [Polynomial.eval_X,entryMeasure]
    omega
  have hd : WorkBound (composition (first (B := (List ℕ×List ℕ)×(List ℕ×List ℕ)))
      denominatorRealizer) entryMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_denominator X
    intro z
    simpa only [Polynomial.eval_X,Function.comp_apply] using (weight_fst z).trans (hi z)
  unfold diagonalEntryRealizer
  apply work_congr
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_second
    polynomial_profileCodeEqual) X hi) hd (work_of_polynomial (polynomial_constant 0) X hi) X hi

def matrixEntry (z : MatrixEntryInput) : ℕ :=
  if profileTest (sourceData z) then validEntry z else diagonalEntry z

def matrixEntryRealizer : Realizer matrixEntry :=
  choose (composition sourceDataRealizer profileTestRealizer) validEntryRealizer diagonalEntryRealizer

lemma work_matrixEntry : WorkBound matrixEntryRealizer entryMeasure := by
  unfold matrixEntryRealizer
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_sourceData
    polynomial_profileTest) X (fun z => by simp only [Polynomial.eval_X,entryMeasure]; omega))
    work_validEntry work_diagonalEntry X (fun z => by simp only [Polynomial.eval_X,entryMeasure]; omega)

end ContingencyTables.UnitCountPrograms

end OAI
