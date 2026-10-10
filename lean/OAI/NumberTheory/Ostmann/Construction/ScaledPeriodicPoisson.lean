import OAI.NumberTheory.Ostmann.Construction.FourierScale
import OAI.NumberTheory.Ostmann.Construction.PeriodicPoisson

namespace OAI

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
open FourierTransform
namespace Ostmann.Construction

theorem scaled_periodic_poisson (Q : ℕ) [NeZero Q]
    (ψ : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ) {X C : ℝ}
    (hX : 0 < X) (hperiod : C*(Q : ℝ)<X)
    (hband : ∀ ξ : ℝ, C < |ξ| → 𝓕 ψ ξ=0) :
    (∑' n : ℤ, periodicResidueTest Q F n * ψ ((n : ℝ)/X)) =
      (X/(Q : ℝ) : ℂ) * 𝓕 ψ 0 * (∑ r, F r) := by
  have hQ : (0 : ℝ)<Q := by exact_mod_cast NeZero.pos Q
  let a : ℝ := Q/X
  have ha : 0<a := div_pos hQ hX
  let f := schwartzScale ψ a ha.ne'
  have hfreq : ∀ n : ℤ, n≠0 → 𝓕 f (n : ℝ)=0 := by
    intro n hn
    rw [schwartzScale_fourier]
    have hnNat : 1≤n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
    have hnInt : (1 : ℤ)≤|n| := by
      simpa only [Int.natCast_natAbs] using
        (show (1 : ℤ)≤(n.natAbs : ℤ) by exact_mod_cast hnNat)
    have hnReal : (1 : ℝ)≤|(n : ℝ)| := by exact_mod_cast hnInt
    have hratio : C<1/a := by
      simpa only [a, one_div, inv_div] using (lt_div_iff₀ hQ).mpr hperiod
    have hlarge : C < |(n : ℝ)/a| := by
      rw [abs_div, abs_of_pos ha]
      exact hratio.trans_le (div_le_div_of_nonneg_right hnReal ha.le)
    rw [hband _ hlarge, smul_zero]
  have hpoisson := periodic_poisson_zero_frequency Q f F hfreq
  have hterm (n : ℤ) : f ((n : ℝ)/Q)=ψ ((n : ℝ)/X) := by
    change ψ (((n : ℝ)/Q)*(Q/X)) = _
    congr 1
    field_simp
  simp_rw [hterm] at hpoisson
  rw [hpoisson]
  change (∑ r, F r) * 𝓕 (schwartzScale ψ a ha.ne') 0 = _
  rw [schwartzScale_fourier, zero_div, abs_of_pos (inv_pos.mpr ha)]
  have hainv : a⁻¹=X/(Q : ℝ) := by simp only [a, inv_div]
  rw [hainv]
  rw [Complex.real_smul, Complex.ofReal_div]
  ring

theorem scaled_periodic_mean_zero (Q : ℕ) [NeZero Q]
    (ψ : SchwartzMap ℝ ℂ) (F : Fin Q → ℂ) {X C : ℝ}
    (hX : 0<X) (hperiod : C*(Q : ℝ)<X)
    (hband : ∀ ξ : ℝ, C < |ξ| → 𝓕 ψ ξ=0) (hmean : ∑ r, F r=0) :
    (∑' n : ℤ, periodicResidueTest Q F n * ψ ((n : ℝ)/X))=0 := by
  rw [scaled_periodic_poisson Q ψ F hX hperiod hband, hmean, mul_zero]

end Ostmann.Construction

end

end OAI
