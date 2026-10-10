import OAI.Combinatorics.ContingencyTables.Machines.BoundedPowerProgram
import OAI.Combinatorics.ContingencyTables.Machines.OffsetCountProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseSuccessCounts

namespace OAI

/-! # Binary evaluation of the offset numerator product -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary FairBits
open scoped BigOperators

/-- A shared bit allowance, widths, actual bit lengths and offsets. -/
abbrev PreparedOffsetData := ((List Bool×List ℕ)×List ℕ)×List ℕ

def preparedOffsetInput (z : PreparedOffsetData×ℕ) : OffsetCountPrograms.Input :=
  ((z.1.1.1.2.getD z.2 0,
    BoundedPowerPrograms.power (z.1.1.1.1,
      z.1.1.1.1.length-z.1.1.2.getD z.2 0)),z.1.2.getD z.2 0)

def preparedOffsetInputRealizer : Realizer preparedOffsetInput := by
  let cap : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let widths : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let lengths : Realizer (fun z : PreparedOffsetData×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let offsets : Realizer (fun z : PreparedOffsetData×ℕ => z.1.2) := composition first second
  let M := composition (pair widths second) (getDFast 0)
  let r := composition (pair lengths second) (getDFast 0)
  let beta := composition (pair offsets second) (getDFast 0)
  let gap := composition (pair (composition cap listLength) r) subtract
  let Q := composition (pair cap gap) BoundedPowerPrograms.powerRealizer
  exact pair (pair M Q) beta

lemma polynomial_preparedOffsetInput : PolynomialTime preparedOffsetInputRealizer := by
  have hcap : PolynomialTime (composition (composition (composition
      (first (A := PreparedOffsetData) (B := ℕ)) first) first) first) := by tree_poly
  have hw : PolynomialTime (composition (composition (composition
      (first (A := PreparedOffsetData) (B := ℕ)) first) first) second) := by tree_poly
  have hr : PolynomialTime (composition (composition
      (first (A := PreparedOffsetData) (B := ℕ)) first) second) := by tree_poly
  have ho : PolynomialTime (composition
      (first (A := PreparedOffsetData) (B := ℕ)) second) := by tree_poly
  have hM := polynomial_composition (polynomial_pair hw polynomial_second) (polynomial_getDFast 0)
  have hR := polynomial_composition (polynomial_pair hr polynomial_second) (polynomial_getDFast 0)
  have hB := polynomial_composition (polynomial_pair ho polynomial_second) (polynomial_getDFast 0)
  have hg := polynomial_composition (polynomial_pair
    (polynomial_composition hcap polynomial_listLength) hR) polynomial_subtract
  have hQ := polynomial_composition (polynomial_pair hcap hg) BoundedPowerPrograms.polynomial_power
  unfold preparedOffsetInputRealizer
  exact polynomial_pair (polynomial_pair hM hQ) hB

def preparedOffsetFactor (z : PreparedOffsetData×ℕ) : ℕ :=
  OffsetCountPrograms.offsetCount (preparedOffsetInput z)

def preparedOffsetFactorRealizer : Realizer preparedOffsetFactor :=
  composition preparedOffsetInputRealizer OffsetCountPrograms.offsetCountRealizer

lemma polynomial_preparedOffsetFactor : PolynomialTime preparedOffsetFactorRealizer :=
  polynomial_composition polynomial_preparedOffsetInput OffsetCountPrograms.polynomial_offsetCount

def preparedOffsetIndices (z : PreparedOffsetData) : List ℕ := List.range z.1.1.2.length

def preparedOffsetIndicesRealizer : Realizer preparedOffsetIndices :=
  composition (composition (composition (composition first first) second) listLength) range

lemma polynomial_preparedOffsetIndices : PolynomialTime preparedOffsetIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))

def preparedOffsetProduct (z : PreparedOffsetData) : ℕ :=
  ((preparedOffsetIndices z).map (fun i => preparedOffsetFactor (z,i))).prod

def preparedOffsetProductRealizer : Realizer preparedOffsetProduct :=
  composition (composition (pair identity preparedOffsetIndicesRealizer)
    (mapWith preparedOffsetFactorRealizer)) listProd

/-- The product uses binary ceiling divisions and shared bounded powers.
It is polynomial in its supplied bit allowance and integer data. -/
theorem polynomial_preparedOffsetProduct : PolynomialTime preparedOffsetProductRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_preparedOffsetIndices)
    (polynomial_mapWith polynomial_preparedOffsetFactor)) polynomial_listProd

lemma preparedOffsetFactor_ofFn {q : ℕ} (cap : List Bool) (w r o : Fin q → ℕ)
    (j : Fin q) (hr : r j≤cap.length) :
    preparedOffsetFactor ((((cap,List.ofFn w),List.ofFn r),List.ofFn o),j.val)=
      OffsetCountPrograms.offsetCount ((w j,2^r j),o j) := by
  unfold preparedOffsetFactor preparedOffsetInput
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  rw [BoundedPowerPrograms.power_eq,Nat.sub_sub_self hr]

private lemma range_prod (f : ℕ → ℕ) (q : ℕ) :
    ((List.range q).map f).prod=∏ j : Fin q,f j.val := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.prod_range_succ,Fin.prod_univ_castSucc,ih]
    rfl

theorem preparedOffsetProduct_ofFn {q : ℕ} (cap : List Bool) (w r o : Fin q → ℕ)
    (hr : ∀ j,r j≤cap.length) :
    preparedOffsetProduct (((cap,List.ofFn w),List.ofFn r),List.ofFn o)=
      ∏ j : Fin q,OffsetCountPrograms.offsetCount ((w j,2^r j),o j) := by
  unfold preparedOffsetProduct preparedOffsetIndices
  rw [List.length_ofFn,range_prod]
  apply Finset.prod_congr rfl
  intro j _
  exact preparedOffsetFactor_ofFn cap w r o j (hr j)

end ContingencyTables.DensePrograms

end OAI
