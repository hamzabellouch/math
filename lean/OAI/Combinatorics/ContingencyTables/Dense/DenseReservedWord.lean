import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

def denseParameterBits (z : DenseDrawParameters) : ℕ :=
  (z.1.2^4*(z.2+1))*trialWidth z

def denseParameterBitsRealizer : Realizer denseParameterBits :=
  composition (pair (composition (pair (composition (composition first second) fourthPower)
    (composition second successor)) multiply) trialWidthRealizer) multiply

theorem polynomial_denseParameterBits : PolynomialTime denseParameterBitsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_fourthPower) (polynomial_composition polynomial_second polynomial_successor))
      polynomial_multiply) polynomial_trialWidth) polynomial_multiply

def preparedCanonicalParameters (z : CanonicalParameters) : DenseDrawParameters :=
  (preparedDraw (canonicalInput (z,[]))).1.1

def preparedCanonicalParametersRealizer : Realizer preparedCanonicalParameters := by
  let blank : Realizer (fun z : CanonicalParameters => (z,([] : List Bool))) :=
    pair identity (constant [])
  let input : Realizer (fun z : CanonicalParameters => canonicalInput (z,[])) :=
    composition (f := fun z : CanonicalParameters => (z,([] : List Bool)))
      (g := canonicalInput) blank canonicalInputRealizer
  let prep : Realizer (fun z : CanonicalParameters => preparedDraw (canonicalInput (z,[]))) :=
    composition (f := fun z : CanonicalParameters => canonicalInput (z,[]))
      (g := preparedDraw) input preparedDrawRealizer
  exact composition (f := fun z : CanonicalParameters => preparedDraw (canonicalInput (z,[])))
    (g := fun z : DenseDrawData => z.1.1) prep (composition first first)

theorem polynomial_preparedCanonicalParameters : PolynomialTime preparedCanonicalParametersRealizer := by
  unfold preparedCanonicalParametersRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_constant [])) polynomial_canonicalInput)
    polynomial_preparedDraw) (polynomial_composition polynomial_first polynomial_first)

def canonicalBitCount (z : CanonicalParameters) : ℕ :=
  denseParameterBits (preparedCanonicalParameters z)

def canonicalBitCountRealizer : Realizer canonicalBitCount :=
  composition preparedCanonicalParametersRealizer denseParameterBitsRealizer

theorem polynomial_canonicalBitCount : PolynomialTime canonicalBitCountRealizer :=
  polynomial_composition polynomial_preparedCanonicalParameters polynomial_denseParameterBits

def reservedCanonicalDraw (z : CanonicalDrawData) : MatrixCode :=
  canonicalDenseDraw (z.1,z.2.take (canonicalBitCount z.1))

def reservedCanonicalDrawRealizer : Realizer reservedCanonicalDraw :=
  composition (pair first (composition (pair second
    (composition first canonicalBitCountRealizer)) takeFast)) canonicalDenseDrawRealizer

theorem polynomial_reservedCanonicalDraw : PolynomialTime reservedCanonicalDrawRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_canonicalBitCount)) polynomial_takeFast))
    polynomial_canonicalDenseDraw

open GridBoundary
open scoped BigOperators Classical
noncomputable section

theorem canonicalBitCount_code {m n d : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 0 < d) (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ) :
    canonicalBitCount ((marginCode R,marginCode P),(d,h))=normalizedDrawBits R P d h := by
  unfold canonicalBitCount preparedCanonicalParameters
  rw [canonicalInput_code R P hd htotal]
  unfold preparedDraw
  rw [drawIndices_code,permuteDrawData_code]
  change (d^4*(h+1))*trialWidth
    ((((marginCode (normalizedMargin R),marginCode (normalizedMargin P)),
      gridNatCode (canonicalOrigin (m*n) d hd)),d),h)=_
  rw [trialWidth_code]
  rfl

lemma take_ofFn_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k=List.ofFn (prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,Nat.min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take,List.getElem_ofFn,prefixWord,Fin.castLE]

theorem reservedCanonicalDraw_code {m n d N : ℕ}
    (R : Option (Fin m) → ℕ) (P : Option (Fin n) → ℕ)
    (hd : 14 ≤ d) (hR : ∀ i,d^12 ≤ R i) (hP : ∀ j,d^12 ≤ P j)
    (htotal : (∑ i,R i)=∑ j,P j) (h : ℕ)
    (hN : normalizedDrawBits R P d h ≤ N) (bits : Fin N → Bool) :
    reservedCanonicalDraw (((marginCode R,marginCode P),(d,h)),List.ofFn bits)=
      tableOutput (normalizedBooleanDraw R P hd hR hP htotal h
        (canonicalOrigin (m*n) d (by omega)) (canonicalFallback R P htotal) (prefixWord hN bits)) := by
  unfold reservedCanonicalDraw
  rw [canonicalBitCount_code R P (by omega) htotal,take_ofFn_prefix hN]
  exact canonicalDenseDraw_eq R P hd hR hP htotal h _

end
end ContingencyTables.DensePrograms

end OAI
