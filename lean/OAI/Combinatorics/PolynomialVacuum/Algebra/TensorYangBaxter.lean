import OAI.Combinatorics.PolynomialVacuum.Algebra.TripleActions
import OAI.Combinatorics.PolynomialVacuum.Algebra.HomogeneousYangBaxter
import OAI.Combinatorics.PolynomialVacuum.Algebra.Unitary

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem matrix_yang_baxter (x y z : ℂ) :
    matrix12 (exchangeNumerator x y) * matrix23 (exchangeNumerator x z) *
      matrix12 (exchangeNumerator y z) =
    matrix23 (exchangeNumerator y z) * matrix12 (exchangeNumerator x z) *
      matrix23 (exchangeNumerator x y) := by
  ext ⟨a,b,c⟩ ⟨d,e,f⟩
  rw [matrix121_apply,matrix232_apply]
  exact homogeneous_yang_baxter_coefficients x y z a b c d e f

theorem tensor_yang_baxter {I : Type*} [DecidableEq I] {i j k : I}
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (x y z : ℂ) (W : SpinTensor I ℂ) :
    pairAction i j (exchangeNumerator x y)
      (pairAction j k (exchangeNumerator x z) (pairAction i j (exchangeNumerator y z) W)) =
    pairAction j k (exchangeNumerator y z)
      (pairAction i j (exchangeNumerator x z) (pairAction j k (exchangeNumerator x y) W)) := by
  rw [← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k,
    ← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k,
    ← tripleAction_matrix12 hik hjk, ← tripleAction_matrix23 i j k]
  simp only [tripleAction_mul hij hik hjk,← Matrix.mul_assoc,matrix_yang_baxter]

theorem tensor_unitarity {I : Type*} [DecidableEq I] {i j : I} (hij : i≠j)
    (x y : ℂ) (W : SpinTensor I ℂ) :
    pairAction i j (exchangeNumerator x y) (pairAction i j (exchangeNumerator y x) W) =
      fun s => (exchangeDenominator x y * exchangeDenominator y x) * W s := by
  rw [pairAction_mul hij,exchange_numerator_unitarity,pairAction_smul,pairAction_one]

theorem tensor_regular {I : Type*} [DecidableEq I] {i j : I} (_hij : i≠j)
    (x : ℂ) (W : SpinTensor I ℂ) :
    pairAction i j (exchangeNumerator x x) W =
      fun s => exchangeDenominator x x * W s := by
  rw [exchange_numerator_regular,pairAction_smul,pairAction_one]

end PolynomialVacuumAlgebra

end OAI
