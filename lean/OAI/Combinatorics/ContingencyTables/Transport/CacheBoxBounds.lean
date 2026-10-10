import OAI.Combinatorics.ContingencyTables.Dense.DenseTabulationScalarBounds
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileMatrixEntryRuntime

namespace OAI

/-! # The finite boxes controlling one cached transition entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms Polynomial

def completionBoxMeasure (z : CanonicalParameters) : ℕ :=
  rawBoxMeasure (canonicalCountInput z).1+
    gridStateCount (completionEnumerationData z.1)+weight z

theorem completionWeightMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    completionWeightMeasure z ≤ p.eval (completionBoxMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_canonicalCountInput
  obtain ⟨q,hq⟩ := rawTabulationMeasure_polynomial
  refine ⟨q+p+2*X,?_⟩
  intro z
  let M := completionBoxMeasure z
  have hz : weight z ≤ M := by unfold M completionBoxMeasure; omega
  have hw : weight (canonicalCountInput z) ≤ p.eval M :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hb : rawBoxMeasure (canonicalCountInput z).1 ≤ M := by
    unfold M completionBoxMeasure; omega
  have hr : rawTabulationMeasure (canonicalCountInput z).1 ≤ q.eval M :=
    (hq (canonicalCountInput z).1).trans (polynomial_eval_monotone q hb)
  have hc : gridStateCount (completionEnumerationData z.1)+weight z.1 ≤ M := by
    have := weight_fst z
    unfold M completionBoxMeasure
    omega
  change rawTabulationMeasure (canonicalCountInput z).1+weight (canonicalCountInput z)+
    weight z+(gridStateCount (completionEnumerationData z.1)+weight z.1) ≤ _
  change _ ≤ (q+p+2*X).eval M
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  omega

end ContingencyTables.DensePrograms

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

def matrixEntryBox (z : MatrixEntryInput) : ℕ :=
  completionBoxMeasure (residualParameters (entryCacheParameters z).1)+
    (entryCacheParameters z).2+gridStateCount (z.1.2,2)+weight z

def entryResidualParameters (z : MatrixEntryInput) : CanonicalParameters :=
  residualParameters (entryCacheParameters z).1

def entryResidualRealizer : Realizer entryResidualParameters :=
  composition (f := fun z : MatrixEntryInput => (entryCacheParameters z).1)
    (g := residualParameters)
    (composition (f := entryCacheParameters) (g := Prod.fst) entryCacheParametersRealizer first)
    residualParametersRealizer

lemma polynomial_entryResidual : PolynomialTime entryResidualRealizer :=
  polynomial_composition (polynomial_composition polynomial_entryCacheParameters polynomial_first)
    polynomial_residualParameters

/-- Separating binary preparation size from the four enumerated boxes. -/
theorem matrixEntryBox_bound : ∃ p : Polynomial ℕ,∀ z,
    let r := entryResidualParameters z
    let a := (canonicalCountInput r).1
    matrixEntryBox z ≤ (4*a.2.1^8)^tabulationDimension a+
      gridStateCount (completionEnumerationData a.1)+
      gridStateCount (completionEnumerationData r.1)+gridStateCount (z.1.2,2)+
      r.2.1+r.2.2+(entryCacheParameters z).2+p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_entryResidual
  obtain ⟨q,hq⟩ := polynomial_canonicalCountInput
  refine ⟨q.comp p+p+X,?_⟩
  intro z
  dsimp only
  have hr : weight (entryResidualParameters z) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans (hp z)
  have ha : weight (canonicalCountInput (entryResidualParameters z)) ≤
      q.eval (p.eval (weight z)) :=
    (Nat.le_add_left _ _).trans ((hq _).trans (polynomial_eval_monotone q hr))
  have hf := (weight_fst (canonicalCountInput (entryResidualParameters z))).trans ha
  change weight (canonicalCountInput (entryResidualParameters z)).1 ≤
    q.eval (p.eval (weight z)) at hf
  simp only [eval_add,eval_comp,eval_X]
  change (4*((canonicalCountInput (entryResidualParameters z)).1).2.1^8)^
      tabulationDimension (canonicalCountInput (entryResidualParameters z)).1+
      gridStateCount (completionEnumerationData (canonicalCountInput (entryResidualParameters z)).1.1)+
      ((entryResidualParameters z).2.1+(entryResidualParameters z).2.2+
        weight (canonicalCountInput (entryResidualParameters z)).1)+
      gridStateCount (completionEnumerationData (entryResidualParameters z).1)+
      weight (entryResidualParameters z)+(entryCacheParameters z).2+
      gridStateCount (z.1.2,2)+weight z ≤ _
  omega

theorem matrixEntryMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    matrixEntryMeasure z ≤ p.eval (matrixEntryBox z) := by
  obtain ⟨p,hp⟩ := polynomial_entryCacheParameters
  obtain ⟨q,hq⟩ := completionWeightMeasure_polynomial
  refine ⟨q+p+X,?_⟩
  intro z
  let M := matrixEntryBox z
  have hz : weight z ≤ M := by unfold M matrixEntryBox; omega
  have hw : weight (entryCacheParameters z) ≤ p.eval M :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hc : completionBoxMeasure (residualParameters (entryCacheParameters z).1) ≤ M := by
    unfold M matrixEntryBox; omega
  have hq' : completionWeightMeasure (residualParameters (entryCacheParameters z).1) ≤
      q.eval M := (hq _).trans (polynomial_eval_monotone q hc)
  have hs : (entryCacheParameters z).2+gridStateCount (z.1.2,2)+weight z ≤ M := by
    unfold M matrixEntryBox; omega
  change (entryCacheParameters z).2+
    completionWeightMeasure (residualParameters (entryCacheParameters z).1)+
    weight (entryCacheParameters z)+gridStateCount (z.1.2,2)+weight z ≤ _
  change _ ≤ (q+p+X).eval M
  simp only [eval_add,eval_X]
  omega

end ContingencyTables.ProfilePrograms

end OAI
