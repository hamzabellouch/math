import OAI.NumberTheory.TwoPoint.Halasz.HalaszModerateCofactor

namespace OAI

/-! The actual original prime bands fit the cofactor inclusion-exclusion
budget even when their cutoff is specified at the original scale. -/
namespace TwoPointCorrelations

open Filter Finset

theorem halasz_cofactor_band_count :
    ∀ᶠ n : ℕ in atTop, ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      (2:ℝ)^(Icc 1 J).card ≤ (Real.log n)^(1/1000:ℝ) := by
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually halasz_band_power_cost,eventually_ge_atTop 2]
    with n hcost hn
  intro X hnX hX Q J hQ hband
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hln : 0 ≤ Real.log (n:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1≤n by omega))
  have hlogX : Real.log (X:ℝ) ≤ 3*Real.log (n:ℝ) := by
    have hh := Real.log_le_log hX0 (show (X:ℝ) ≤ (n:ℝ)^3 by exact_mod_cast hX)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hsqrt : Real.sqrt (Real.log (X:ℝ)) ≤ 2*Real.sqrt (Real.log (n:ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hln]
  have hupper : Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt (Real.log (n:ℝ)) := by
    have hpos : 0 < mrtBandUpper Q J := by unfold mrtBandUpper; positivity
    have hh := Real.log_le_log hpos hband
    rw [Real.log_exp] at hh
    exact hh.trans hsqrt
  have hh := hcost Q J hQ hupper
  simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hh

/-- The moderate-frequency cofactor bound for the actual original bands. -/
theorem halasz_moderate_actual_cofactor :
    ∃ X₀ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N:ℝ)/a⌋₊:ℝ) →
      n = ⌊(2*N:ℝ)/a⌋₊ → ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∀ t τ : ℝ,
      (∀ v : ℝ, |v| ≤ X → squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X) →
      |t|+(Real.log n)^8 ≤ X →
      |t-τ|+(Real.log n)^8 ≤ (Real.log X)^20 →
      (Real.log n)^(1/16:ℝ)/2 ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        (Real.log n)^(-1/40:ℝ) := by
  obtain ⟨X₀,hcofactor⟩ := halasz_moderate_cofactor
  refine ⟨X₀,?_⟩
  filter_upwards [hcofactor,halasz_cofactor_band_count] with n hcofactor hcount
  intro N a ha hbase hn X hnX hX F hF1 hFm hFb P Q J hQ hband A hA t τ hmin ht hmod haway
  exact hcofactor N a ha hbase hn X hnX hX F hF1 hFm hFb ℕ (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) A
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hA (hcount X hnX hX Q J hQ hband)
    t τ hmin ht hmod haway

end TwoPointCorrelations

end OAI
