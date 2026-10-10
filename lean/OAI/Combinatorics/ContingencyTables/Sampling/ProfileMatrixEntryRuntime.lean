import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixEntry

namespace OAI

/-! # Finite-box work bound for the executable transition entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] prepareTransitionCache prepareTransitionCacheRealizer
  entryCacheParameters entryCacheParametersRealizer transitionCount transitionCountRealizer
  entryQueryRealizer

def matrixEntryMeasure (z : MatrixEntryInput) : ℕ :=
  transitionCacheMeasure (entryCacheParameters z)+gridStateCount (z.1.2,2)+weight z

private lemma input_le_measure (z : MatrixEntryInput) : weight z ≤ matrixEntryMeasure z := by
  unfold matrixEntryMeasure
  omega

private lemma polynomial_work {B : Type} [Codec B] {f : MatrixEntryInput → B}
    {F : Realizer f} (hF : PolynomialTime F) : WorkBound F matrixEntryMeasure :=
  work_of_polynomial hF X (fun z => by simpa using input_le_measure z)

lemma work_entryCache : WorkBound
    (composition entryCacheParametersRealizer prepareTransitionCacheRealizer) matrixEntryMeasure := by
  apply work_composition (polynomial_work polynomial_entryCacheParameters)
    work_prepareTransitionCache X
  intro z
  simp only [Polynomial.eval_X,matrixEntryMeasure]
  omega

lemma work_entryQuery : WorkBound entryQueryRealizer matrixEntryMeasure := by
  have hi (z : MatrixEntryInput) : weight z ≤ X.eval (matrixEntryMeasure z) := by
    simpa using input_le_measure z
  have ht : WorkBound (composition (second (A := MatrixParameters)) second)
      matrixEntryMeasure := polynomial_work
    (polynomial_composition polynomial_second polynomial_second)
  have hb : WorkBound (composition (first (B := (List ℕ×List ℕ)×(List ℕ×List ℕ))) second)
      matrixEntryMeasure := polynomial_work
    (polynomial_composition polynomial_first polynomial_second)
  have hp := work_pair work_entryCache ht X hi
  unfold entryQueryRealizer
  exact work_pair hp hb X hi

lemma work_validMatrixEntry : WorkBound validMatrixEntryRealizer matrixEntryMeasure := by
  obtain ⟨p,hp⟩ := work_entryQuery
  unfold validMatrixEntryRealizer
  apply work_composition ⟨p,hp⟩ work_transitionCount (X+p)
  intro z
  have hw := hp z
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change gridStateCount (z.1.2,2)+weight (entryQuery z) ≤ _
  have hg : gridStateCount (z.1.2,2) ≤ matrixEntryMeasure z := by
    unfold matrixEntryMeasure
    omega
  omega

lemma work_matrixDenominator : WorkBound matrixDenominatorRealizer
    (fun z : MatrixParameters => z.2.length+z.1.2+weight z) := by
  have hi : WorkBound (pair (constant 2) (composition (pair
      (composition (second (A := TransitionCacheParameters)) listLength)
      (composition first second)) add))
      (fun z : MatrixParameters => z.2.length+z.1.2+weight z) :=
    work_of_polynomial (polynomial_pair (polynomial_constant 2)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_listLength)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_add)) X
      (fun z => by simp only [Polynomial.eval_X]; omega)
  unfold matrixDenominatorRealizer
  apply work_composition hi BinaryPowerPrograms.work_power (X+9)
  intro z
  change z.2.length+z.1.2+weight (2:ℕ) ≤ (X+9).eval _
  have htwo : weight (2:ℕ) ≤ 9 := by simpa using weight_nat_numeric 2
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

lemma work_entryDenominator : WorkBound
    (composition (first (B := (List ℕ×List ℕ)×(List ℕ×List ℕ)))
      matrixDenominatorRealizer) matrixEntryMeasure := by
  apply work_composition (polynomial_work polynomial_first) work_matrixDenominator (2*X)
  intro z
  have hl := (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))
  have hf : z.1.1.2 ≤ transitionCacheMeasure (entryCacheParameters z) := by
    unfold transitionCacheMeasure entryCacheParameters
    omega
  have hw := weight_fst z
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,matrixEntryMeasure]
  omega

lemma work_diagonalMatrixEntry : WorkBound diagonalMatrixEntryRealizer matrixEntryMeasure := by
  unfold diagonalMatrixEntryRealizer
  apply work_congr
  exact work_choose
    (polynomial_work (polynomial_composition polynomial_second polynomial_profileCodeEqual))
    work_entryDenominator (polynomial_work (polynomial_constant 0))
    X (fun z => by simpa using input_le_measure z)

lemma work_matrixEntry : WorkBound matrixEntryRealizer matrixEntryMeasure := by
  unfold matrixEntryRealizer
  apply work_choose
    (polynomial_work (polynomial_composition polynomial_sourceData polynomial_profileTest)) _
    work_diagonalMatrixEntry X (fun z => by simpa using input_le_measure z)
  exact work_choose
    (polynomial_work (polynomial_composition polynomial_targetData polynomial_profileTest))
    work_validMatrixEntry (polynomial_work (polynomial_constant 0))
    X (fun z => by simpa using input_le_measure z)

end ContingencyTables.ProfilePrograms

end OAI
