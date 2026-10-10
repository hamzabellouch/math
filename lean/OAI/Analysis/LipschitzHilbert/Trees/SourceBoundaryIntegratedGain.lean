import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryErrorDecay

namespace OAI

/-! The entropy prefactor in the original boundary error fits any
prescribed negative-power budget after all fixed exponents are chosen. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem eventually_boundary_integrated_gain (D q m Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ a Nmass Fmass S : ℝ,
      0 ≤ a → a ≤ 1 → 0 ≤ Nmass → 0 ≤ Fmass → S ≤ L^m*Nmass*Fmass →
      (8*a*L^q*(4*SourceParameters.step L^(-(1/4:ℝ)))*((2:ℝ)^D)^7*(1+2*L))*S ≤
        L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_boundary_error_power_budget (24*((2:ℝ)^D)^7) (q+m+1) Q]
    with L hL hbudget
  intro a Nmass Fmass S ha ha1 hN hF hS
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let eps := 4*SourceParameters.step L^(-(1/4:ℝ))
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  have hcoef : 0 ≤ 8*a*L^q*eps*((2:ℝ)^D)^7*(1+2*L) := by positivity
  have hsmall : 8*a*(1+2*L) ≤ 24*L := by
    have h := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 8*(1+2*L) by positivity)
    nlinarith
  have hpower : L^(q+m+1) = L^q*L^m*L := by
    rw [Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
  have hc : (8*a*L^q*eps*((2:ℝ)^D)^7*(1+2*L))*L^m ≤
      (24*((2:ℝ)^D)^7)*L^(q+m+1)*eps := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ L^q*L^m*eps*((2:ℝ)^D)^7 by positivity)
    rw [hpower]
    convert hh using 1 <;> ring
  calc
    _ ≤ (8*a*L^q*eps*((2:ℝ)^D)^7*(1+2*L))*(L^m*Nmass*Fmass) :=
      mul_le_mul_of_nonneg_left hS hcoef
    _ = ((8*a*L^q*eps*((2:ℝ)^D)^7*(1+2*L))*L^m)*(Nmass*Fmass) := by ring
    _ ≤ ((24*((2:ℝ)^D)^7)*L^(q+m+1)*eps)*(Nmass*Fmass) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hN hF)
    _ ≤ L^(-Q)*(Nmass*Fmass) := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hN hF)
    _ = _ := by ring

/-- The boundary budget with the polynomial slack required at log ratio 2L. -/
theorem eventually_boundary_integrated_gain_wide (D q m Q : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ a Nmass Fmass S : ℝ,
      0 ≤ a → a ≤ 1 → 0 ≤ Nmass → 0 ≤ Fmass → S ≤ L^m*Nmass*Fmass →
      (8*a*L^q*(4*SourceParameters.step L^(-(1/4:ℝ)))*((2:ℝ)^D)^7*(1+3*L))*S ≤
        L^(-Q)*Nmass*Fmass := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_boundary_error_power_budget (32*((2:ℝ)^D)^7) (q+m+1) Q]
    with L hL hbudget
  intro a Nmass Fmass S ha ha1 hN hF hS
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let eps := 4*SourceParameters.step L^(-(1/4:ℝ))
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (SourceParameters.step_pos L).le _)
  have hcoef : 0 ≤ 8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L) := by positivity
  have hsmall : 8*a*(1+3*L) ≤ 32*L := by
    have h := mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 8*(1+3*L) by positivity)
    nlinarith
  have hpower : L^(q+m+1) = L^q*L^m*L := by
    rw [Real.rpow_add hL0,Real.rpow_add hL0,Real.rpow_one]
  have hc : (8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*L^m ≤
      (32*((2:ℝ)^D)^7)*L^(q+m+1)*eps := by
    have hh := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ L^q*L^m*eps*((2:ℝ)^D)^7 by positivity)
    rw [hpower]
    convert hh using 1 <;> ring
  calc
    _ ≤ (8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*(L^m*Nmass*Fmass) :=
      mul_le_mul_of_nonneg_left hS hcoef
    _ = ((8*a*L^q*eps*((2:ℝ)^D)^7*(1+3*L))*L^m)*(Nmass*Fmass) := by ring
    _ ≤ ((32*((2:ℝ)^D)^7)*L^(q+m+1)*eps)*(Nmass*Fmass) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hN hF)
    _ ≤ L^(-Q)*(Nmass*Fmass) := mul_le_mul_of_nonneg_right hbudget (mul_nonneg hN hF)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI
