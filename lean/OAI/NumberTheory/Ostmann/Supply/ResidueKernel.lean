import OAI.NumberTheory.Ostmann.Supply.CenteredProjection
import OAI.NumberTheory.Ostmann.Supply.Fourier

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def complementRatio (S : Finset (ZMod p)) : ℝ := (p : ℝ) / S.card - 1

theorem complementRatio_eq_density (S : Finset (ZMod p)) (hS : S.Nonempty) :
    complementRatio S = (1-density S)/density S := by
  have hsR : (S.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hS
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  simp only [complementRatio, density, ZMod.card]
  field_simp

theorem complementRatio_nonneg (S : Finset (ZMod p)) (hS : S.Nonempty) :
    0 ≤ complementRatio S := by
  have hs : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have hcard : (S.card : ℝ) ≤ p := by
    exact_mod_cast (Finset.card_le_univ S).trans_eq (ZMod.card p)
  exact sub_nonneg.mpr ((le_div_iff₀ hs).mpr (by simpa using hcard))

theorem primeKernel_centered (S : Finset (ZMod p)) (x y : ZMod p)
    (hx : x ∈ S) (hy : y ∈ S) :
    (p : ℂ)*(if x=y then 1 else 0)-1 =
      (p : ℂ)*inner ℂ
        (centeredProjection S (EuclideanSpace.single x (1 : ℂ)))
        (centeredProjection S (EuclideanSpace.single y (1 : ℂ))) + complementRatio S := by
  rw [centeredProjection_gram S x y hx hy]
  simp only [complementRatio, Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_one]
  ring

theorem primeKernel_eq_nonzero_sum (x y : ZMod p) :
    (∑ h ∈ Finset.univ.erase 0, ZMod.stdAddChar (h*(x-y))) =
      (p : ℂ)*(if x=y then 1 else 0)-1 := by
  have hsum : ∑ h : ZMod p, ZMod.stdAddChar (h*(x-y)) =
      if x=y then (p:ℂ) else 0 := by
    by_cases hxy : x=y
    · simp [hxy]
    · have ht : x-y ≠ 0 := sub_ne_zero.mpr hxy
      have hh := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p ht)
      simpa only [AddChar.mulShift_apply, mul_comm, hxy, ite_false] using hh
  have hz : ZMod.stdAddChar ((0:ZMod p)*(x-y)) = 1 := by simp
  have hh := Finset.sum_erase_add (Finset.univ) (fun h:ZMod p => ZMod.stdAddChar (h*(x-y)))
    (Finset.mem_univ 0)
  rw [hsum,hz] at hh
  split_ifs with hxy <;> simp_all
  linear_combination hh

end Ostmann.Supply

end

end OAI
