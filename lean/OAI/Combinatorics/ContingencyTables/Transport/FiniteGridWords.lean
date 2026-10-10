import OAI.Combinatorics.ContingencyTables.Machines.BinaryPowerProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisSemantics

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

abbrev GridEnumerationData := List Bool×ℕ

def clippedGridPowerInput (z : GridEnumerationData×ℕ) : ℕ×ℕ :=
  (z.1.2,min z.2 z.1.1.length)

def clippedGridPowerInputRealizer : Realizer clippedGridPowerInput :=
  pair (composition first second)
    (composition (pair second (composition (composition first first) listLength)) minNat)

lemma polynomial_clippedGridPowerInput : PolynomialTime clippedGridPowerInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_listLength)) polynomial_minNat)

def clippedGridPower (z : GridEnumerationData×ℕ) : ℕ :=
  BinaryPowerPrograms.power (clippedGridPowerInput z)

def clippedGridPowerRealizer : Realizer clippedGridPower :=
  composition clippedGridPowerInputRealizer BinaryPowerPrograms.powerRealizer

lemma polynomial_clippedGridPower : PolynomialTime clippedGridPowerRealizer := by
  apply work_composition polynomial_clippedGridPowerInput BinaryPowerPrograms.work_power
    (2*Polynomial.X)
  intro z
  have hl := (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))
  have hw := (weight_snd z.1).trans (weight_fst z)
  have hm := min_le_right z.2 z.1.1.length
  simp only [clippedGridPowerInput,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

abbrev GridCoordinateData := (GridEnumerationData×ℕ)×ℕ

def gridCoordinate (z : GridCoordinateData) : ℕ :=
  z.1.2 / clippedGridPower (z.1.1,z.2) % z.1.1.2

def gridCoordinateRealizer : Realizer gridCoordinate :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair (composition first first) second) clippedGridPowerRealizer)) quotient)
    (composition (composition first first) second)) remainder

lemma polynomial_gridCoordinate : PolynomialTime gridCoordinateRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_clippedGridPower)) polynomial_quotient)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)) polynomial_remainder

def gridCoordinateIndices (z : GridEnumerationData×ℕ) : List ℕ := List.range z.1.1.length

def gridCoordinateIndicesRealizer : Realizer gridCoordinateIndices :=
  composition (composition (composition first first) listLength) range

lemma polynomial_gridCoordinateIndices : PolynomialTime gridCoordinateIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_first polynomial_first) polynomial_listLength) Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def gridCoordinates (z : GridEnumerationData×ℕ) : List ℕ :=
  (gridCoordinateIndices z).map (fun i => gridCoordinate (z,i))

def gridCoordinatesRealizer : Realizer gridCoordinates :=
  composition (pair identity gridCoordinateIndicesRealizer) (mapWith gridCoordinateRealizer)

lemma polynomial_gridCoordinates : PolynomialTime gridCoordinatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_gridCoordinateIndices)
    (polynomial_mapWith polynomial_gridCoordinate)

def gridStateCount (z : GridEnumerationData) : ℕ :=
  clippedGridPower (z,z.1.length)

def gridStateCountRealizer : Realizer gridStateCount :=
  composition (pair identity (composition first listLength)) clippedGridPowerRealizer

lemma polynomial_gridStateCount : PolynomialTime gridStateCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_clippedGridPower

lemma gridStateCount_eq (z : GridEnumerationData) : gridStateCount z=z.2^z.1.length := by
  simp [gridStateCount,clippedGridPower,clippedGridPowerInput,BinaryPowerPrograms.power_eq]

def gridWords (z : GridEnumerationData) : List (List ℕ) :=
  (List.range (gridStateCount z)).map (fun i => gridCoordinates (z,i))

def gridWordsRealizer : Realizer gridWords :=
  composition (pair identity (composition gridStateCountRealizer range))
    (mapWith gridCoordinatesRealizer)

/-- State enumeration is polynomial in its output count, not in the
precision or number of fair random words of the sampler. -/
theorem work_gridWords : WorkBound gridWordsRealizer
    (fun z => gridStateCount z+weight z) := by
  have hp : WorkBound gridStateCountRealizer (fun z => gridStateCount z+weight z) :=
    work_of_polynomial polynomial_gridStateCount Polynomial.X (fun z => by simp)
  have hr : WorkBound (composition gridStateCountRealizer range)
      (fun z => gridStateCount z+weight z) :=
    work_composition hp range_numeric_work Polynomial.X (fun z => by simp)
  unfold gridWordsRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_gridCoordinates)
  apply work_pair
    (work_of_polynomial polynomial_identity Polynomial.X (fun z => by simp)) hr
    Polynomial.X (fun z => by simp)

private lemma map_range_eq_ofFn {A : Type*} (f : ℕ → A) (N : ℕ) :
    (List.range N).map f=List.ofFn (fun i : Fin N => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range N) f).symm

lemma gridCoordinates_eq (z : GridEnumerationData) (x : ℕ) :
    gridCoordinates (z,x)=List.ofFn
      (fun i : Fin z.1.length => x/z.2^i.val % z.2) := by
  rw [gridCoordinates,gridCoordinateIndices,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [gridCoordinate,clippedGridPower,clippedGridPowerInput,
    BinaryPowerPrograms.power_eq]

def gridDigitEquiv (K : ℕ) : Fin K ≃ Set.Icc (0:ℤ) ((K:ℤ)-1) where
  toFun x := ⟨(x.val:ℤ),by
    change 0≤(x.val:ℤ) ∧ (x.val:ℤ)≤(K:ℤ)-1
    have hx := x.isLt
    omega⟩
  invFun x := ⟨x.val.toNat,by
    have hx0 : 0≤x.val := x.property.1
    have hxK : x.val≤(K:ℤ)-1 := x.property.2
    omega⟩
  left_inv x := by ext; simp
  right_inv x := by
    apply Subtype.ext
    have hx0 : 0≤x.val := x.property.1
    dsimp
    omega

def gridEnumeration (q K : ℕ) : Fin (K^q) ≃ Grid (I := Fin q) K :=
  finFunctionFinEquiv.symm.trans (Equiv.piCongrRight (fun _ => gridDigitEquiv K))

lemma gridEnumeration_code (q K : ℕ) (a : Fin (K^q)) :
    gridNatCode (gridEnumeration q K a)=
      List.ofFn (fun i : Fin q => a.val/K^i.val % K) := by
  apply congrArg List.ofFn
  funext i
  rfl

/-- Every box state occurs once in this explicit, mixed-radix list. -/
theorem gridWords_eq (z : GridEnumerationData) :
    gridWords z=List.ofFn (fun i => gridNatCode (gridEnumeration z.1.length z.2 i)) := by
  unfold gridWords
  rw [gridStateCount_eq,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [gridCoordinates_eq,gridEnumeration_code]

lemma gridWords_eq_length (xs : List Bool) (K q : ℕ) (hq : xs.length=q) :
    gridWords (xs,K)=List.ofFn (fun i => gridNatCode (gridEnumeration q K i)) := by
  subst q
  exact gridWords_eq (xs,K)

end ContingencyTables.DensePrograms

end OAI
