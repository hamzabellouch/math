import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedPauli
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedPauliProgram

namespace OAI

/-! Fixed-width algebraic coefficient tables, with exact normalization of
the padded words. Each local arity at most six uses a fixed finite program. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedTable
open QuantumAlgebraicScalar QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem coefficient_decision {ι : Type} [Fintype ι]
    (d e : DecidableEq ι) (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (w : ι → Fin 4) (r : ℝ) :
    r * (@qmaPauliCoefficient ι _ d A w).re =
      r * (@qmaPauliCoefficient ι _ e A w).re := by
  cases Subsingleton.elim d e
  rfl

def coefficient (n m : ℕ) (xs : List Scalar) (w : Fin (n+m) → Fin 4) : RealScalar :=
  let v := QuantumPaddedPauli.restrictWord n m w
  if Even (qmaPauliYCount v) then
    realMul (realRat (((4:ℚ)^m)⁻¹))
      (realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t) v)
  else realRat 0

noncomputable opaque coefficientProgram (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Procedure matrixCode realCode (fun xs => coefficient n m xs w) := by
  by_cases h : Even (qmaPauliYCount (QuantumPaddedPauli.restrictWord n m w))
  · exact (realMulProgram.comp
      ((Procedure.constant matrixCode realCode (realRat (((4:ℚ)^m)⁻¹))).pair
        (realCoefficientProgram n (QuantumPaddedPauli.restrictWord n m w)))).congrFun
          (by intro xs; simp only [coefficient,h,ite_true,Function.comp_apply])
  · exact (Procedure.constant matrixCode realCode (realRat 0)).congrFun
      (by intro xs; simp only [coefficient,h,ite_false])

def table (n m : ℕ) (xs : List Scalar) : List RealScalar :=
  (enumerate (Fin (n+m) → Fin 4)).map (coefficient n m xs)

noncomputable def tableProgram (n m : ℕ) :
    Procedure matrixCode (listCode realCode) (table n m) :=
  (QuantumRawExchange.fixedListProgram matrixCode realCode
    (Fintype.card (Fin (n+m) → Fin 4))
    (fun i xs => coefficient n m xs ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i))
    (fun i => coefficientProgram n m ((Fintype.equivFin (Fin (n+m) → Fin 4)).symm i))).congrFun
      (by intro xs; simp only [table,enumerate,List.map_ofFn,Function.comp_def])

theorem coefficient_value (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar)
    (w : Fin (n+m) → Fin 4) :
    realValue (coefficient n m (matrixData A) w) =
      QuantumPaddedPauli.paddedCoefficient n m (fun s t => value (A s t)) w := by
  let v := QuantumPaddedPauli.restrictWord n m w
  by_cases h : Even (qmaPauliYCount v)
  · simp only [coefficient,show Even (qmaPauliYCount
        (QuantumPaddedPauli.restrictWord n m w)) from h,ite_true,
        realValue_mul,realValue_rat,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat]
    rw [QuantumFixedPauli.coefficient_matrixData]
    simp only [QuantumPaddedPauli.paddedCoefficient,QuantumPaddedPauli.evenCoefficient,
      show Even (qmaPauliYCount (QuantumPaddedPauli.restrictWord n m w)) from h,ite_true]
    simp only [div_eq_mul_inv,mul_comm]
    exact coefficient_decision _ _ _ _ _
  · simp only [coefficient,show ¬Even (qmaPauliYCount
        (QuantumPaddedPauli.restrictWord n m w)) from h,ite_false,realValue_rat,
        Rat.cast_zero,QuantumPaddedPauli.paddedCoefficient,
        QuantumPaddedPauli.evenCoefficient,zero_div]

theorem table_length (n m : ℕ) (xs : List Scalar) :
    (table n m xs).length = 4^(n+m) := by
  simp only [table,List.length_map,enumerate,List.length_ofFn,Fintype.card_fun,
    Fintype.card_fin]

theorem six_table_length (n : ℕ) (hn : n ≤ 6) (xs : List Scalar) :
    (table n (6-n) xs).length = 4096 := by
  rw [table_length,Nat.add_sub_of_le hn]
  norm_num

noncomputable def certificate (n m : ℕ) :
    Turing.TM2ComputableInPolyTime matrixCode (listCode realCode) (table n m) :=
  (tableProgram n m).toTM2

abbrev Input := ℕ × List Scalar
def inputCode : Input → List Bool := prodCode Nat.bits matrixCode

/-- Total fixed-arity dispatcher. Invalid arities use the six-site branch. -/
def uniformTable (x : Input) : List RealScalar :=
  if x.1=0 then table 0 6 x.2 else
  if x.1=1 then table 1 5 x.2 else
  if x.1=2 then table 2 4 x.2 else
  if x.1=3 then table 3 3 x.2 else
  if x.1=4 then table 4 2 x.2 else
  if x.1=5 then table 5 1 x.2 else table 6 0 x.2

noncomputable opaque uniformProgram :
    Procedure inputCode (listCode realCode) uniformTable := by
  let arity := Procedure.first Nat.bits matrixCode
  let rows := Procedure.second Nat.bits matrixCode
  let is (n : ℕ) := Procedure.binaryEq.comp
    (arity.pair (Procedure.constant inputCode Nat.bits n))
  let out (n m : ℕ) := (tableProgram n m).comp rows
  exact (Procedure.conditional (is 0) (out 0 6)
    (Procedure.conditional (is 1) (out 1 5)
    (Procedure.conditional (is 2) (out 2 4)
    (Procedure.conditional (is 3) (out 3 3)
    (Procedure.conditional (is 4) (out 4 2)
    (Procedure.conditional (is 5) (out 5 1) (out 6 0))))))).congrFun (by
      intro x
      simp only [uniformTable,Function.comp_apply,decide_eq_true_eq])

theorem uniformTable_eq (n : ℕ) (hn : n ≤ 6) (xs : List Scalar) :
    uniformTable (n,xs) = table n (6-n) xs := by
  interval_cases n <;> norm_num [uniformTable]

theorem uniformTable_length (n : ℕ) (hn : n ≤ 6) (xs : List Scalar) :
    (uniformTable (n,xs)).length = 4096 := by
  rw [uniformTable_eq n hn xs]
  exact six_table_length n hn xs

noncomputable def uniformCertificate :
    Turing.TM2ComputableInPolyTime inputCode (listCode realCode) uniformTable :=
  uniformProgram.toTM2

end ContinuumCoulomb.QuantumPaddedTable

end

end OAI
