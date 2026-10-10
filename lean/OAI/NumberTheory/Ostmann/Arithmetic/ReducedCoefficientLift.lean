import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticResidueReversal

namespace OAI

/-! # Using the remaining precision of reconstructed pivots in later coefficients -/

namespace Ostmann

open scoped BigOperators

/-- An arbitrary representative at the original modulus. Its reduction
is independent of this lift whenever the remaining precision suffices. -/
def liftResidueRepresentative (Q M : ℕ) (x : ZMod M) : ZMod Q := x.val

theorem reduce_liftResidueRepresentative (Q M d : ℕ) [NeZero M]
    (hdQ : d ∣ Q) (hdM : d ∣ M) (x : ZMod M) :
    ZMod.castHom hdQ (ZMod d) (liftResidueRepresentative Q M x) =
      ZMod.castHom hdM (ZMod d) x := by
  have h := congrArg (ZMod.castHom hdM (ZMod d)) (ZMod.natCast_zmod_val x)
  simpa only [liftResidueRepresentative, map_natCast] using h

theorem reduce_liftResidueRepresentative_int (Q M d : ℕ) [NeZero M]
    (hdQ : d ∣ Q) (hdM : d ∣ M) (x : ZMod M) (a : ℤ) (hx : x = a) :
    ZMod.castHom hdQ (ZMod d) (liftResidueRepresentative Q M x) = a := by
  rw [reduce_liftResidueRepresentative Q M d hdQ hdM x, hx, map_intCast]

/-- A known nonbulk coefficient can include any specified finite set of
ancestor pivots. Multiplication loses no further frequency precision. -/
theorem reduce_ancestor_product {I : Type*} [Fintype I]
    (Q M d : ℕ) [NeZero M] (hdQ : d ∣ Q) (hdM : d ∣ M)
    (C : ℤ) (x : I → ZMod M) (a : I → ℤ) (hx : ∀ i, x i = a i) :
    ZMod.castHom hdQ (ZMod d)
      ((C : ZMod Q) * ∏ i, liftResidueRepresentative Q M (x i)) =
      ((C * ∏ i, a i : ℤ) : ZMod d) := by
  rw [map_mul, map_prod, map_intCast]
  simp only [Int.cast_mul, Int.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact reduce_liftResidueRepresentative_int Q M d hdQ hdM (x i) (a i) (hx i)

/-- After at most k divisions, the remaining R-power still contains each
frequency divisor, so lifted ancestor coefficients can be tested modulo it. -/
theorem frequency_dvd_remaining_precision (R s k depth : ℕ)
    (hs : s ∣ R) (hdepth : depth ≤ k + 1) : s ∣ R ^ (k + 2 - depth) := by
  exact hs.trans (dvd_pow_self R (by omega))

end Ostmann

end OAI
