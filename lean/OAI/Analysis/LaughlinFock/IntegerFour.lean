import Mathlib
import OAI.Analysis.LaughlinFock.CertificateRows
import OAI.Analysis.LaughlinFock.FastWedge
import OAI.Analysis.LaughlinFock.IntegerCoupling

namespace OAI

/-! Integer Four. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def integerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    integerCoupling 1 r (j+k-r) j * integerCoupling 1 (D-r) (T-D) p
  else 0

theorem rationalCopyPolynomial_integer (D T r p j k : ℕ) :
    rationalCopyPolynomial D T r p j k = (integerCopyPolynomial D T r p j k : ℚ) := by
  simp only [rationalCopyPolynomial, integerCopyPolynomial, apply_ite (fun z:ℤ => (z:ℚ)),
    Int.cast_mul, ← rationalCoupling_integer, Int.cast_one, Int.cast_zero]

def integerFourTrace (D t : ℕ) (a : RowEntry t → ℚ) :
    Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  -(∑ b : RowEntry t, ∑ c : RowEntry t, if D ≤ rowFourLevel b c then
    a b*a c*rationalFourFactor D b c *
      (integerCopyPolynomial D (rowFourLevel b c) r.val.val (rowP b) (rowJ b) (rowI c) : ℚ) *
      (integerCopyPolynomial D (rowFourLevel b c) s.val.val (rowP c) (rowJ c) (rowI b) : ℚ)
    else 0)

theorem rationalFourTrace_integer (D t : ℕ) (a : RowEntry t → ℚ) :
    rationalFourTrace D t a = integerFourTrace D t a := by
  ext r s
  simp only [rationalFourTrace, integerFourTrace, rationalCopyPolynomial_integer]

def integerRowsFourTrace (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  ∑ t : Fin 8, integerFourTrace D t.val (certificateAlpha t)

def integerHighestTerm (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) : ℚ :=
  if x<y ∧ j<k ∧ (x.val+y.val-1)+j.val+k.val=D then
    (integerCopyPolynomial D D r.val.val (x.val+y.val-1) j.val k.val : ℚ) *
      ((x.val:ℚ)-(y.val:ℚ)) * (x.val+y.val-1).factorial * j.val.factorial * k.val.factorial *
      rationalWordVacuum [x,y,j,k] A
  else 0

theorem fastHighestTerm_integer (D : ℕ) (r : CopyLabel D) (A : Occupation 24)
    (x y j k : Orbital 24) :
    fastHighestTerm D r A x y j k = integerHighestTerm D r A x y j k := by
  unfold fastHighestTerm integerHighestTerm
  split_ifs with hh
  · have hxy : x.val+y.val=(x.val+y.val-1)+1 := by
      have := hh.1
      change x.val<y.val at this
      omega
    simp only [rationalHighestTerm, ite_eq_left hxy, rationalCopyPolynomial_integer]
  · rfl

def integerHighestEntry (D : ℕ) (r : CopyLabel D) (A : Occupation 24) : ℚ :=
  ∑ j ∈ A, ∑ k ∈ A, ∑ x ∈ A, ∑ y ∈ A, integerHighestTerm D r A x y j k

def integerFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ := fun r s =>
  ∑ A ∈ highestFourOccupations D,
    2 * integerHighestEntry D r A * integerHighestEntry D s A /
      (2^(2*D) * occupationFactorial A)

theorem rationalFourGram_integer (D : ℕ) : rationalFourGram D = integerFourGram D := by
  rw [rationalFourGram_fast]
  ext r s
  simp only [fastFourGram, integerFourGram, fastHighestEntry, integerHighestEntry,
    fastHighestTerm_integer]

 

def integerFourMiddle (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  Matrix.diagonal (fun r => ((if r.val.val=1 then 2 else 0)+3/10^6) *
    rationalCopyDiagonal D r.val.val) -
    Matrix.diagonal (fun r : CopyLabel D => rationalCopyDiagonal D r.val.val) *
      integerRowsFourTrace D * Matrix.diagonal (fun r : CopyLabel D => rationalCopyDiagonal D r.val.val)

def integerCompression (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℚ :=
  integerFourGram D * integerFourMiddle D * integerFourGram D

end LaughlinFock
end

end OAI
