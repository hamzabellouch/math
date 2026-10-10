import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementError
import OAI.NumberTheory.Ostmann.QuadraticSieveDualSquareLattice

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap FourierTransform

theorem squarePullback_integral (W : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, squarePullback W 1 (by norm_num) x) =
      2 * (∫ x : ℝ in Ioi 0, W (x ^ 2)) := by
  let f : ℝ → ℂ := fun x => W (x ^ 2)
  have hf : Integrable f := by
    simpa only [one_mul] using integrable_squarePullback W (show (1 : ℝ) ≠ 0 by norm_num)
  have heq : (∫ x : ℝ in Iic 0, f x) = ∫ x : ℝ in Ioi 0, f x := by
    calc
      _ = ∫ x : ℝ in Ioi 0, f (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 f).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [f, neg_sq]
  simp only [squarePullback_apply, one_mul]
  change (∫ x : ℝ, f x) = 2 * ∫ x : ℝ in Ioi 0, f x
  rw [← integral_add_compl (s := Ioi 0) measurableSet_Ioi hf, compl_Ioi, heq]
  ring

theorem squarePullback_zero_of_positive_support (W : 𝓢(ℝ, ℂ))
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) : squarePullback W 1 (by norm_num) 0 = 0 := by
  simp only [squarePullback_apply, zero_pow (by omega : 2 ≠ 0), mul_zero]
  by_contra hn
  have hm := hs (subset_tsupport W (Function.mem_support.mpr hn))
  exact (lt_irrefl (0 : ℝ)) hm

theorem complementary_totient_factor (q d : ℕ) (hq : Odd q) (hd : Odd d)
    (hcop : Nat.Coprime q d) :
    (Nat.totient (2 * q * d) : ℂ) / (2 * q * d : ℕ) =
      ((Nat.totient q : ℂ) / (q : ℂ)) * ((Nat.totient d : ℂ) / (d : ℂ)) / 2 := by
  rw [Nat.mul_assoc, Nat.totient_two_mul_of_odd (hq.mul hd), Nat.totient_mul hcop]
  push_cast
  ring

theorem coprimePoissonMain_square (W : 𝓢(ℝ, ℂ))
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (k : ℕ) (X Y Z L : ℝ) :
    coprimePoissonMain (squarePullback W 1 (by norm_num)) k X Y Z L =
      (Nat.totient k : ℂ) / (k : ℂ) * (X : ℂ) *
        (2 * ∫ x : ℝ in Ioi 0, W (x ^ 2))
      - (X : ℂ) * (2 * ∫ x : ℝ in Ioi 0, W (x ^ 2)) *
        (∑ d ∈ k.divisors.filter (fun d : ℕ => Z < (d : ℝ)),
          (ArithmeticFunction.moebius d : ℂ) / (d : ℂ))
      + (∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ) ∧ (d : ℝ) ≤ Z),
          (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
            ∑ l ∈ nonzeroIntegerCutoff L,
              𝓕 (squarePullback W 1 (by norm_num)) ((l : ℝ) * (X / d))) := by
  rw [coprimePoissonMain, squarePullback_integral, squarePullback_zero_of_positive_support W hs]
  simp only [zero_mul, sub_zero]

end Ostmann.QuadraticSieve

end OAI
