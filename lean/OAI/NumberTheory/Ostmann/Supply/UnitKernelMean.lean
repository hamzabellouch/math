import OAI.NumberTheory.Ostmann.Supply.ContractionConstants
import OAI.NumberTheory.Ostmann.Supply.KernelMoments

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

def unitKernelMean (S : Finset (ZMod p)) (t : ℝ) : ℝ :=
  (∑ x ∈ Finset.univ.erase 0, (1+localKernel S t x)^2)/((p:ℝ)-1)

theorem unitKernelMean_lower (S : Finset (ZMod p)) {t ε : ℝ}
    (hp : 2 ≤ p) (_ht : 0 ≤ t) (ht' : t ≤ 1) (hε : 0 ≤ ε)
    (hc : ((largeSpectrum S).card:ℝ)/p ≤ ε) :
    1-4*ε/(p:ℝ)  ≤  unitKernelMean S t := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hpm : 0<(p:ℝ)-1 := by linarith
  have he : 0 ≤ ((largeSpectrum S).card:ℝ)/p := div_nonneg (Nat.cast_nonneg _) hp0.le
  have hcard : ((Finset.univ.erase (0:ZMod p)).card:ℝ) = (p:ℝ)-1 := by
    simp [Finset.card_erase_of_mem,ZMod.card,Nat.cast_sub (show 1 ≤ p by omega)]
  have hsum : ∑ x ∈ Finset.univ.erase 0, (1+localKernel S t x)^2 =
      ((p:ℝ)-1)+2*(∑ x ∈ Finset.univ.erase 0,localKernel S t x)+
      ∑ x ∈ Finset.univ.erase 0,(localKernel S t x)^2 := by
    simp only [add_sq,one_pow,mul_one,Finset.sum_add_distrib,
      Finset.sum_const,nsmul_eq_mul,mul_one,←Finset.mul_sum,hcard]
  have hsq : 0 ≤ ∑ x ∈ Finset.univ.erase 0,(localKernel S t x)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsmall : 2*t*(((largeSpectrum S).card:ℝ)/p)  ≤  2*ε := by
    have htE : t*(((largeSpectrum S).card:ℝ)/p)  ≤  ε :=
      (mul_le_mul_of_nonneg_right ht' he).trans (by simpa using hc)
    linarith
  have hsmall' : 2*ε/((p:ℝ)-1)  ≤  4*ε/(p:ℝ) := by
    apply (div_le_div_iff₀ hpm hp0).mpr
    nlinarith [mul_nonneg hε (show 0 ≤ (p:ℝ)-2 by linarith)]
  have hsmall'' := (div_le_div_of_nonneg_right hsmall hpm.le).trans hsmall'
  unfold unitKernelMean
  rw [hsum,localKernel_nonzero_sum]
  apply (le_div_iff₀ hpm).mpr
  have hh := (div_le_iff₀ hpm).mp hsmall''
  simp only [mul_div_assoc] at hh ⊢
  nlinarith

theorem sparse_unitKernelMean_lower (S : Finset (ZMod p)) {t : ℝ}
    (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hpos : 0<density S) (hlt : density S<1) (hg : gamma S ≤ supplyEpsilon^2) :
    1-4*supplyEpsilon/(p:ℝ) ≤ unitKernelMean S t := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hc := (sparse_transform_concentration S hpos hlt supplyEpsilon_pos.le supplyEpsilon_le_one hg).1
  exact unitKernelMean_lower S hp ht ht' supplyEpsilon_pos.le ((div_le_iff₀ hp0).mpr hc)

theorem sparse_unitKernelMean_pos (S : Finset (ZMod p)) {t : ℝ}
    (hp : 2 ≤ p) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hpos : 0<density S) (hlt : density S<1) (hg : gamma S ≤ supplyEpsilon^2) :
    0<unitKernelMean S t := by
  have h := sparse_unitKernelMean_lower S hp ht ht' hpos hlt hg
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hh : 4*supplyEpsilon/(p:ℝ)<1 := by
    apply (div_lt_iff₀ hp0).mpr
    norm_num only [supplyEpsilon] at ⊢
    linarith
  linarith

end Ostmann.Supply

end

end OAI
