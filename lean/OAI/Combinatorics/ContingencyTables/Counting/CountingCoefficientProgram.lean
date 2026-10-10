import OAI.Combinatorics.ContingencyTables.Counting.CountingTerminalSchedule
import OAI.Combinatorics.ContingencyTables.Machines.OffsetCountProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreeFractionCosts

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

abbrev Input := (ℕ×ℕ)×Fraction

def precision (e : Fraction) : ℕ := Nat.clog 2 (ceilQuotient (e.2,e.1))
def precisionRealizer : Realizer precision :=
  composition (f := fun e : Fraction => ceilQuotient (e.2,e.1)) (g := Nat.clog 2)
    (composition (pair second first) ceilQuotientRealizer) ceilLogTwoRealizer
lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      polynomial_ceilQuotient) polynomial_ceilLogTwo

def allowance (z : Input) : ℕ := 20*(z.1.1+z.1.2+precision z.2+1)
def allowanceRealizer : Realizer allowance := by
  let ld : Realizer (fun z : Input => z.1.1+z.1.2) := composition first add
  let pr : Realizer (fun z : Input => precision z.2) :=
    composition (f := fun z : Input => z.2) (g := precision) second precisionRealizer
  let s : Realizer (fun z : Input => z.1.1+z.1.2+precision z.2+1) :=
    composition (composition (pair ld pr) add) successor
  exact composition (f := fun z : Input => (20,z.1.1+z.1.2+precision z.2+1))
    (g := fun p : ℕ×ℕ => p.1*p.2) (pair (constant 20) s) multiply
lemma polynomial_allowance : PolynomialTime allowanceRealizer := by
  unfold allowanceRealizer
  exact polynomial_composition (polynomial_pair (polynomial_constant 20)
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first TreeTyped.polynomial_add)
        (polynomial_composition polynomial_second polynomial_precision)) TreeTyped.polynomial_add)
      polynomial_successor)) polynomial_multiply

def numerator (z : Input) : ℕ := 2048*z.1.2*(allowance z)^2*z.2.2
def numeratorRealizer : Realizer numerator := by
  let d : Realizer (fun z : Input => 2048*z.1.2) :=
    composition (f := fun z : Input => (2048,z.1.2))
      (g := fun p : ℕ×ℕ => p.1*p.2)
      (pair (constant 2048) (composition first second)) multiply
  let sq : Realizer (fun z : Input => (allowance z)^2) :=
    (composition (pair allowanceRealizer allowanceRealizer) multiply).congr
      (fun z => (pow_two _).symm)
  exact composition (pair (composition (pair d sq) multiply) (composition second second)) multiply
lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2048)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)
      (polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_allowance polynomial_allowance) polynomial_multiply)))
      polynomial_multiply)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply

def coefficient (z : Input) : ℕ := ceilQuotient (numerator z,z.2.1)
def coefficientRealizer : Realizer coefficient :=
  composition (f := fun z : Input => (numerator z,z.2.1)) (g := ceilQuotient)
    (pair numeratorRealizer (composition second first)) ceilQuotientRealizer
lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator
    (polynomial_composition polynomial_second polynomial_first)) polynomial_ceilQuotient

lemma precision_val (e : Fraction) (hn : 0 < e.1) :
    precision e=CountingTerminalSchedule.precision (val e) := by
  unfold precision CountingTerminalSchedule.precision
  rw [ceilQuotient_eq e.2 e.1 hn]
  congr 2
  simp only [val,one_div,inv_div]

lemma allowance_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) :
    allowance ((L,d),e)=CountingTerminalSchedule.allowance L d (val e) := by
  simp only [allowance,CountingTerminalSchedule.allowance,precision_val e hn]

lemma coefficient_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) (hd : 0 < e.2) :
    coefficient ((L,d),e)=CountingTerminalSchedule.coefficient L d (val e) := by
  unfold coefficient
  rw [ceilQuotient_eq _ _ hn]
  unfold CountingTerminalSchedule.coefficient
  rw [←allowance_val L d e hn]
  congr 1
  simp only [numerator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,val]
  field_simp

lemma coefficient_repr (L d : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient ((L,d),TreeFraction.repr epsilon)=
      CountingTerminalSchedule.coefficient L d epsilon := by
  have hn : 0 < (TreeFraction.repr epsilon).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  rw [coefficient_val L d _ hn epsilon.pos,TreeFraction.val_repr he.le]

end ContingencyTables.CountingCoefficientProgram

end OAI
