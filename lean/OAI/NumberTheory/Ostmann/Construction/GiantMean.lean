import OAI.NumberTheory.Ostmann.Construction.GiantPhase

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction
variable {p : ℕ} [NeZero p]

def giantTestReal (S : Finset (ZMod p)) (x : ZMod p) : ℝ := (giantTest S x).re

theorem giantTestReal_sum_zero (S : Finset (ZMod p)) : ∑ x, giantTestReal S x = 0 := by
  simpa only [Complex.re_sum, Complex.zero_re, giantTestReal] using
    congrArg Complex.re (giantTest_sum_zero S)

theorem giantTestReal_sq_sum_le (S : Finset (ZMod p)) :
    (∑ x, (giantTestReal S x)^2) ≤ p := by
  have heq (x : ZMod p) : ‖giantTest S x‖^2 = (giantTestReal S x)^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, giantTest_real, mul_zero, add_zero,
      giantTestReal, pow_two]
  simpa only [heq] using giantTest_sum_sq_le S

theorem giantTestReal_pairing (S : Finset (ZMod p)) :
    (∑ x, Supply.normalizedIndicator S x * giantTestReal S x) =
      ∑ v, ‖Supply.additiveTransform S v‖ := by
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, giantTestReal] using congrArg Complex.re (giantTest_pairing S)

theorem giantTestReal_sum_support (S : Finset (ZMod p))
    (hpos : 0 < Supply.density S) (hlt : Supply.density S < 1) :
    (∑ x ∈ S, giantTestReal S x) =
      Real.sqrt (Supply.density S*(1-Supply.density S)) *
        (∑ v, ‖Supply.additiveTransform S v‖) := by
  let σ := Supply.density S
  have hvar : 0 < σ*(1-σ) := mul_pos hpos (sub_pos.mpr hlt)
  have hsqrt : Real.sqrt (σ*(1-σ)) ≠ 0 := (Real.sqrt_pos.mpr hvar).ne'
  have hpair := giantTestReal_pairing S
  have hpoint (x : ZMod p) : Supply.normalizedIndicator S x * giantTestReal S x =
      ((if x∈S then giantTestReal S x else 0)-σ*giantTestReal S x) /
        Real.sqrt (σ*(1-σ)) := by
    dsimp [Supply.normalizedIndicator, Supply.centeredIndicator, σ]
    split_ifs <;> ring
  simp_rw [hpoint] at hpair
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    giantTestReal_sum_zero, mul_zero, sub_zero] at hpair
  simp only [Finset.sum_ite_mem, Finset.univ_inter] at hpair
  exact (div_eq_iff hsqrt).mp hpair |>.trans (mul_comm _ _)

end Ostmann.Construction

end

end OAI
