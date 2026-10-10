import OAI.Combinatorics.ContingencyTables.Dense.DenseEnumeratedMatrix
import OAI.Combinatorics.ContingencyTables.Transport.UnaryMarkers
import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalSemantics

namespace OAI

/-! # Canonical dense-walk tabulation from binary margins and precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev TabulationData := CanonicalParameters

def tabulationDimension (z : TabulationData) : ℕ :=
  z.1.1.tail.length*z.1.2.tail.length

def tabulationSteps (z : TabulationData) : ℕ := z.2.1^50*(z.2.2+1)^2

def tabulationStepsRealizer : Realizer tabulationSteps := by
  let d : Realizer (fun z : TabulationData => z.2.1) := composition second first
  let h : Realizer (fun z : TabulationData => z.2.2) := composition second second
  exact (composition (pair (composition d fiftiethPower)
    (composition (composition h successor) squareNat)) multiply).congr (by
      intro z; simp only [Function.comp_apply,tabulationSteps,Nat.succ_eq_add_one,pow_two])

lemma polynomial_tabulationSteps : PolynomialTime tabulationStepsRealizer := by
  unfold tabulationStepsRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_fiftiethPower)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_successor)
      polynomial_squareNat)) polynomial_multiply

def tabulationAllowance (z : TabulationData) : ℕ := 8*z.2.1^5

def tabulationAllowanceRealizer : Realizer tabulationAllowance := by
  let d : Realizer (fun z : TabulationData => z.2.1) := composition second first
  let result := composition (pair (constant 8) (composition d fifthPower)) multiply
  exact result

lemma polynomial_tabulationAllowance : PolynomialTime tabulationAllowanceRealizer := by
  have hd : PolynomialTime (composition
      (second (A := List ℕ×List ℕ) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_second polynomial_first
  unfold tabulationAllowanceRealizer
  exact polynomial_composition (polynomial_pair (polynomial_constant 8)
    (polynomial_composition hd polynomial_fifthPower)) polynomial_multiply

def tabulationDenominatorInput (z : TabulationData) : ℕ×ℕ :=
  (2,denseStepBits z.2.1)

def tabulationDenominatorInputRealizer : Realizer tabulationDenominatorInput :=
  pair (constant 2) (composition (composition second first) denseWidthRealizer)

lemma polynomial_tabulationDenominatorInput : PolynomialTime tabulationDenominatorInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition
    (polynomial_composition polynomial_second polynomial_first) polynomial_denseWidth)

def tabulationDenominator (z : TabulationData) : ℕ :=
  BinaryPowerPrograms.power (tabulationDenominatorInput z)

def tabulationDenominatorRealizer : Realizer tabulationDenominator :=
  composition tabulationDenominatorInputRealizer BinaryPowerPrograms.powerRealizer

def tabulationDimensions (z : TabulationData) : List Bool :=
  (zeroGrid z.1).map (fun _ => false)

def tabulationDimensionsRealizer : Realizer tabulationDimensions := by
  let grid := composition (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) zeroGridRealizer
  let result := composition grid (map (constant false))
  exact result

lemma polynomial_tabulationDimensions : PolynomialTime tabulationDimensionsRealizer := by
  unfold tabulationDimensionsRealizer
  exact polynomial_composition (polynomial_composition polynomial_first polynomial_zeroGrid)
    (polynomial_map (polynomial_constant false))

lemma tabulationDimensions_length (z : TabulationData) :
    (tabulationDimensions z).length=tabulationDimension z := by
  simp [tabulationDimensions,zeroGrid,cellPairs,tabulationDimension]

def tabulationCountInput (z : TabulationData) : EnumeratedMatrixInput :=
  ((((unaryMarkers (tabulationAllowance z),tabulationDenominator z),
      (z.1,z.2.1))),tabulationDimensions z)

def tabulationCountInputRealizer : Realizer tabulationCountInput := by
  let marks := composition tabulationAllowanceRealizer unaryMarkersRealizer
  let header := pair (pair marks tabulationDenominatorRealizer)
    (pair (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) (composition second first))
  exact pair header tabulationDimensionsRealizer

def tabulationMeasure (z : TabulationData) : ℕ :=
  (4*z.2.1^8)^tabulationDimension z+tabulationAllowance z+
    denseStepBits z.2.1+tabulationSteps z+weight z

private lemma weight_le_measure (z : TabulationData) : weight z≤tabulationMeasure z := by
  unfold tabulationMeasure
  omega

private lemma polynomial_work {X : Type} [Codec X] {f : TabulationData → X}
    {F : Realizer f} (hF : PolynomialTime F) : WorkBound F tabulationMeasure :=
  work_of_polynomial hF Polynomial.X (by intro z; simpa using weight_le_measure z)

private lemma paired_work {X Y : Type} [Codec X] [Codec Y]
    {f : TabulationData → X} {g : TabulationData → Y} {F : Realizer f} {G : Realizer g}
    (hF : WorkBound F tabulationMeasure) (hG : WorkBound G tabulationMeasure) :
    WorkBound (pair F G) tabulationMeasure :=
  work_pair hF hG Polynomial.X (by intro z; simpa using weight_le_measure z)

lemma work_tabulationDenominator : WorkBound tabulationDenominatorRealizer tabulationMeasure := by
  apply work_composition (polynomial_work polynomial_tabulationDenominatorInput)
    BinaryPowerPrograms.work_power (Polynomial.X+9)
  intro z
  have hw : weight (2:ℕ)≤9 := by decide
  simp only [tabulationDenominatorInput,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_ofNat,tabulationMeasure]
  omega

lemma work_tabulationCountInput : WorkBound tabulationCountInputRealizer tabulationMeasure := by
  have ha : WorkBound (composition tabulationAllowanceRealizer unaryMarkersRealizer)
      tabulationMeasure := by
    apply work_composition (polynomial_work polynomial_tabulationAllowance)
      work_unaryMarkers Polynomial.X
    intro z
    simp only [id_eq,Polynomial.eval_X,tabulationMeasure]
    omega
  unfold tabulationCountInputRealizer
  exact paired_work (paired_work (paired_work ha work_tabulationDenominator)
    (polynomial_work (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first))))
    (polynomial_work polynomial_tabulationDimensions)

lemma tabulation_enumerationMeasure (z : TabulationData) :
    enumerationMeasure (tabulationCountInput z)=
      (4*z.2.1^8)^tabulationDimension z+weight (tabulationCountInput z) := by
  simp only [enumerationMeasure,enumerationData,tabulationCountInput,gridStateCount_eq,
    tabulationDimensions_length]

lemma work_tabulationEnumeration : WorkBound
    (composition tabulationCountInputRealizer enumeratedMatrixInputRealizer) tabulationMeasure := by
  obtain ⟨p,hp⟩ := work_tabulationCountInput
  apply work_composition ⟨p,hp⟩ work_enumeratedMatrixInput (Polynomial.X+p)
  intro z
  rw [tabulation_enumerationMeasure]
  have hw := hp z
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  unfold tabulationMeasure at *
  omega

def tabulationInput (z : TabulationData) : MatrixWalkData :=
  ((unaryMarkers (tabulationSteps z),enumeratedMatrixInput (tabulationCountInput z)),zeroGrid z.1)

def tabulationInputRealizer : Realizer tabulationInput := by
  let steps := composition tabulationStepsRealizer unaryMarkersRealizer
  let enum := composition tabulationCountInputRealizer enumeratedMatrixInputRealizer
  let grid := composition (first (A := List ℕ×List ℕ) (B := ℕ×ℕ)) zeroGridRealizer
  exact pair (pair steps enum) grid

lemma work_tabulationInput : WorkBound tabulationInputRealizer tabulationMeasure := by
  have ht : WorkBound (composition tabulationStepsRealizer unaryMarkersRealizer)
      tabulationMeasure := by
    apply work_composition (polynomial_work polynomial_tabulationSteps)
      work_unaryMarkers Polynomial.X
    intro z
    simp only [id_eq,Polynomial.eval_X,tabulationMeasure]
    omega
  unfold tabulationInputRealizer
  exact paired_work (paired_work ht work_tabulationEnumeration)
    (polynomial_work (polynomial_composition polynomial_first polynomial_zeroGrid))

def tabulateDenseWalk (z : TabulationData) : List ℕ := matrixWalk (tabulationInput z)

def tabulateDenseWalkRealizer : Realizer tabulateDenseWalk :=
  composition tabulationInputRealizer matrixWalkRealizer

/-- Binary matrix propagation computes all walk numerators in polynomial
work in the explicit state count and the scheduled number of steps. -/
theorem work_tabulateDenseWalk : WorkBound tabulateDenseWalkRealizer tabulationMeasure :=
  work_then_polynomial work_tabulationInput polynomial_matrixWalk

lemma tabulationDimension_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (d h : ℕ) :
    tabulationDimension ((marginCode R,marginCode P),(d,h))=m*n := by
  simp [tabulationDimension,marginCode]

/-- The caller computes its grid, zero starting state and full iteration
schedule from the margins. No state list or probability oracle is supplied. -/
theorem tabulateDenseWalk_actual {m n d : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d) (hd : 0<d) (h : ℕ) :
    tabulateDenseWalk ((marginCode R,marginCode P),(d,h))=
      List.ofFn (fun i => IntegerPropagation.numerators
        (denseTransitionCount R P d finProdFinEquiv)
        (canonicalOrigin (m*n) d hd) (d^50*(h+1)^2)
        (gridEnumeration (m*n) (4*d^8) i)) := by
  let e := gridEnumeration (m*n) (4*d^8)
  let start := e.symm (canonicalOrigin (m*n) d hd)
  have he : e start=canonicalOrigin (m*n) d hd := e.apply_symm_apply _
  have hdim : (tabulationDimensions ((marginCode R,marginCode P),(d,h))).length=m*n := by
    rw [tabulationDimensions_length,tabulationDimension_code]
  unfold tabulateDenseWalk tabulationInput enumeratedMatrixInput enumerationData
  simp only [tabulationCountInput,tabulationDenominator,tabulationDenominatorInput,
    BinaryPowerPrograms.power_eq]
  rw [gridWords_eq_length _ _ _ hdim,zeroGrid_code R P hd,←he]
  rw [matrixWalk_actual R P hq e _ _ (by simp [tabulationAllowance,unaryMarkers_length]) start]
  simp only [unaryMarkers_length,tabulationSteps,he,e]

end ContingencyTables.DensePrograms

end OAI
