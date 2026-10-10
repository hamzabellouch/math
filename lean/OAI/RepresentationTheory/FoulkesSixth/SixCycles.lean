import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.SourceNewton

namespace OAI

noncomputable section

namespace Foulkes.Complete
open MvPolynomial Finset

def cycleSix {R : Type*} [CommRing R] (p : ℕ → R) : R :=
  p 1 ^ 6 + 15*p 1^4*p 2 + 45*p 1^2*p 2^2 + 15*p 2^3 +
  40*p 1^3*p 3 + 120*p 1*p 2*p 3 + 40*p 3^2 +
  90*p 1^2*p 4 + 90*p 2*p 4 + 144*p 1*p 5 + 120*p 6

theorem cycleSix_of_newton {R : Type*} [CommRing R] (h p : ℕ → R)
    (h0 : h 0 = 1)
    (hn : ∀ j : ℕ, (j : R)*h j = ∑ i ∈ Finset.Icc 1 j, p i*h (j-i)) :
    720*h 6 = cycleSix p := by
  have n1 := hn 1
  have n2 := hn 2
  have n3 := hn 3
  have n4 := hn 4
  have n5 := hn 5
  have n6 := hn 6
  norm_num [Finset.sum_Icc_succ_top, h0] at n1 n2 n3 n4 n5 n6
  have e2 : 2*h 2 = p 1^2+p 2 := by
    linear_combination n2 + p 1*n1
  have e3 : 6*h 3 = p 1^3+3*p 1*p 2+2*p 3 := by
    linear_combination 2*n3 + p 1*e2 + 2*p 2*n1
  have e4 : 24*h 4 = p 1^4+6*p 1^2*p 2+3*p 2^2+8*p 1*p 3+6*p 4 := by
    linear_combination 6*n4 + p 1*e3 + 3*p 2*e2 + 6*p 3*n1
  have e5 : 120*h 5 = p 1^5+10*p 1^3*p 2+15*p 1*p 2^2+
      20*p 1^2*p 3+20*p 2*p 3+30*p 1*p 4+24*p 5 := by
    linear_combination 24*n5 + p 1*e4 + 4*p 2*e3 + 12*p 3*e2 + 24*p 4*n1
  unfold cycleSix
  linear_combination 120*n6 + p 1*e5 + 5*p 2*e4 + 20*p 3*e3 + 60*p 4*e2 + 120*p 5*n1

theorem pleth_cycleSix (n b : ℕ) :
    (720 : ℤ) • pleth n 6 b =
      cycleSix (fun i => Foulkes.Strips.completePowers n i b) := by
  norm_num only [zsmul_eq_mul, Int.cast_ofNat]
  apply cycleSix_of_newton (h := fun j => pleth n j b)
  · exact pleth_zero n b
  · intro j
    simpa only [zsmul_eq_mul, Int.cast_natCast] using pleth_newton_powers n j b

end Foulkes.Complete

end

end OAI
