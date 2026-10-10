import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNearMaskSum

namespace OAI

/-! The actual MRT band count absorbs the finite near-mask sum into a
uniform logarithmic error while retaining the centered typical amplitude. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

/-- Near-center renormalization for the literal family of original bands.
The `-3/50` exponent leaves room for the finite inclusion-exclusion cost. -/
theorem mrt_band_near_renormalization :
    ∀ᶠ N : ℕ in atTop, ∀ P Q : ℝ, ∀ J : ℕ,
      1≤Real.log Q → 1≤J →
      (∀ j∈Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log N))) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ τ : ℝ, squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        Real.log (Real.log (2*N:ℕ))/10 →
      ∀ u : ℝ, |u|≤(Real.log N)^(1/16:ℝ) → ∀ k∈Icc N (2*N),
      ‖halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) τ) u k -
        (halaszPowerPhase u k/(1+(-u:ℂ)*Complex.I))*
          halaszPhaseMean (halaszTwistedFunction (mrtTypicalCoefficient (Icc 1 J)
            (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) τ) 0 k‖ ≤
        (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
          (Real.log N)^(-3/50:ℝ)*k := by
  have hlog : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [mrt_typical_near_renormalization,hlog.eventually halasz_band_power_cost,
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with N hnear hcost hLN
  intro P Q J hQ hJ hmax F hF1 hFm hFb τ hsmall u hu k hk
  have hupper : Real.log (mrtBandUpper Q J) ≤ 2*Real.sqrt (Real.log N) := by
    have hh := Real.log_le_log (show 0 < mrtBandUpper Q J from Real.exp_pos _)
      (hmax J (mem_Icc.mpr ⟨hJ,le_rfl⟩))
    rw [Real.log_exp] at hh
    linarith [Real.sqrt_nonneg (Real.log (N:ℝ))]
  have hcount : (2:ℝ)^(Icc 1 J).card ≤ (Real.log N)^(1/1000:ℝ) := by
    simpa using hcost Q J hQ hupper
  have hb : ∀ j∈Icc 1 J, ∀ p∈mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j),
      (p:ℝ)≤Real.exp (Real.sqrt (Real.log N)) := by
    intro j hj p hp
    exact ((mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp).2).trans (hmax j hj)
  have hh := hnear (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hb F hF1 hFm hFb τ hsmall u hu k hk
  have hL0 : 0<Real.log (N:ℝ) := by linarith
  have hc : 0≤36*(halaszPrimePowerLogConstant+1)*Real.exp 8 := by
    unfold halaszPrimePowerLogConstant
    positivity
  apply hh.trans
  calc
    _ ≤ (Real.log N)^(1/1000:ℝ) * (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
        (Real.log N)^(-1/16:ℝ)*k := by gcongr
    _ = (36*(halaszPrimePowerLogConstant+1)*Real.exp 8) *
        ((Real.log N)^(1/1000:ℝ)*(Real.log N)^(-1/16:ℝ))*k := by ring
    _ ≤ _ := by
      rw [← Real.rpow_add hL0]
      have hp := Real.rpow_le_rpow_of_exponent_le hLN
        (show (1/1000:ℝ)+(-1/16:ℝ)≤(-3/50:ℝ) by norm_num)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (Nat.cast_nonneg k)

end TwoPointCorrelations

end OAI
