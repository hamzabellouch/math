import OAI.NumberTheory.Ostmann.Supply.SpectralProjection

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

theorem unitaryDFT_twice (f : ZMod p → ℂ) (v : ZMod p) :
    unitaryDFT (unitaryDFT f) v = f (-v) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hs : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp.le
  have hs0 : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  change ZMod.dft (fun j => ZMod.dft f j / (Real.sqrt p : ℂ)) v /
    (Real.sqrt p : ℂ) = f (-v)
  simp only [div_eq_mul_inv, ZMod.dft_mul_const, ZMod.dft_dft, smul_eq_mul]
  field_simp
  rw [hs]
  ring

theorem fourierEquiv_symm_apply (f : H) (v : ZMod p) :
    fourierEquiv.symm f v = unitaryDFT f (-v) := by
  have hh : unitaryDFT (fourierEquiv.symm f) = (fun x => f x) := by
    funext x
    rw [← fourierEquiv_apply, LinearIsometryEquiv.apply_symm_apply]
  have h := unitaryDFT_twice (fun x => fourierEquiv.symm f x) (-v)
  rw [hh, neg_neg] at h
  exact h.symm

def fourierKernel (E : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ h ∈ E, ZMod.stdAddChar (h*x)

theorem spectralProjection_apply (E : Finset (ZMod p)) (f : H) (x : ZMod p) :
    spectralProjection E f x = ∑ y, fourierKernel E (x-y) * f y := by
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hs : (Real.sqrt p : ℂ)^2 = (p : ℂ) := by exact_mod_cast Real.sq_sqrt hp
  rw [spectralProjection_eq_maskedFourier]
  simp only [maskedFourier, fourierEquiv_symm_apply, unitaryDFT, ZMod.dft_apply,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_mem,
    Finset.univ_inter, mul_neg, neg_neg]
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [fourierKernel, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro h hh
  rw [mul_sub, AddChar.map_sub_eq_div]
  rw [div_eq_mul_inv, ← AddChar.map_neg_eq_inv]
  rw [show -(y*h) = -(h*y) by ring]
  have hi : (Real.sqrt p : ℂ)⁻¹ * (Real.sqrt p : ℂ)⁻¹ = (p : ℂ)⁻¹ := by
    rw [← mul_inv, ← sq, hs]
  calc
    _ = ((Real.sqrt p : ℂ)⁻¹ * (Real.sqrt p : ℂ)⁻¹) *
        (ZMod.stdAddChar (h*x) * ZMod.stdAddChar (-(h*y))) * f y := by ring
    _ = _ := by rw [hi]

end Ostmann.Supply

end

end OAI
