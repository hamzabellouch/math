import Mathlib

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def density (S : Finset ι) : ℝ := (S.card : ℝ) / Fintype.card ι

def centeredIndicator (S : Finset ι) (x : ι) : ℝ :=
  (if x ∈ S then 1 else 0) - density S

def normalizedIndicator (S : Finset ι) (x : ι) : ℝ :=
  centeredIndicator S x / Real.sqrt (density S * (1 - density S))

theorem sum_indicator (S : Finset ι) :
    ∑ x : ι, (if x ∈ S then (1 : ℝ) else 0) = S.card := by
  simp

theorem sum_centeredIndicator [Nonempty ι] (S : Finset ι) :
    ∑ x, centeredIndicator S x = 0 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [centeredIndicator, Finset.sum_sub_distrib, sum_indicator,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, density]
  field_simp
  ring

theorem sum_centeredIndicator_sq [Nonempty ι] (S : Finset ι) :
    ∑ x, (centeredIndicator S x)^2 =
      Fintype.card ι * (density S * (1 - density S)) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs (x : ι) : (if x ∈ S then (1 : ℝ) else 0)^2 =
      (if x ∈ S then (1 : ℝ) else 0) := by split_ifs <;> norm_num
  simp_rw [centeredIndicator, sub_sq, hs]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_indicator, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, density]
  field_simp
  ring

theorem sum_normalizedIndicator [Nonempty ι] (S : Finset ι) :
    ∑ x, normalizedIndicator S x = 0 := by
  simp only [normalizedIndicator, ← Finset.sum_div, sum_centeredIndicator, zero_div]

theorem sum_normalizedIndicator_sq [Nonempty ι] (S : Finset ι)
    (hpos : 0 < density S) (hlt : density S < 1) :
    ∑ x, (normalizedIndicator S x)^2 = Fintype.card ι := by
  have hv : 0 < density S * (1-density S) := mul_pos hpos (sub_pos.mpr hlt)
  simp only [normalizedIndicator, div_pow, ← Finset.sum_div,
    Real.sq_sqrt hv.le, sum_centeredIndicator_sq]
  exact mul_div_cancel_right₀ _ hv.ne'
end Finite

section Cyclic
variable {p : ℕ} [NeZero p]

def unitaryDFT (f : ZMod p → ℂ) (v : ZMod p) : ℂ :=
  ZMod.dft f v / (Real.sqrt p : ℂ)

def additiveTransform (S : Finset (ZMod p)) : ZMod p → ℂ :=
  unitaryDFT (fun x => (normalizedIndicator S x : ℂ))

def gamma (S : Finset (ZMod p)) : ℝ :=
  (∑ v, ‖additiveTransform S v‖) / p

theorem additiveTransform_zero (S : Finset (ZMod p)) :
    additiveTransform S 0 = 0 := by
  simp only [additiveTransform, unitaryDFT, ZMod.dft_apply_zero]
  rw [← Complex.ofReal_sum, sum_normalizedIndicator]
  simp

theorem gamma_nonneg (S : Finset (ZMod p)) : 0 ≤ gamma S := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Nat.cast_nonneg _)

end Cyclic
end Ostmann.Supply

end

end OAI
