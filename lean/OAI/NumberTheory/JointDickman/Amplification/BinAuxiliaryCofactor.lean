import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryPowerSeparation
import OAI.NumberTheory.JointDickman.Amplification.BinCofactorBound

namespace OAI

/-! # Cofactor cancellation in every bin of the actual auxiliary band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem bin_auxiliary_cofactor {J : ℕ} (hJ : 0 < J)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
    (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
    (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ᶠ N : ℕ in atTop,
      ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ ζ : Fin (J-1) → ℂ, (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, T ≤ |t| → |t| ≤ N →
      ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w)
        N (mrtPrimeLogLower H k) t‖ ≤ ε := by
  have hc : 0 < α/4 := by positivity
  have hc1 : α/4 ≤ 1 := by linarith
  have hroot : 0 < (1:ℝ)/J := by positivity
  obtain ⟨T,K,hT,_hK,hbound⟩ := bin_cofactor_away_zero hJ hc hc1 E hE hε
  refine ⟨T,hT,?_⟩
  have hdiv : Tendsto (fun N : ℕ => (N:ℝ)/A) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hA
  have hcut := (eventually_scaled_power_lt (show α/4<α by linarith)
    (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ)<1)).filter_mono tendsto_natCast_atTop_atTop
  have hscale := (eventually_scaled_power_lt (show α/4<(1:ℝ)/J by linarith)
    (by norm_num : (0:ℝ)<2) hA).filter_mono tendsto_natCast_atTop_atTop
  have hfinite : ∀ᶠ N : ℕ in atTop, ∀ p ∈ E,
      (p:ℝ) ≤ (N:ℝ)^α ∧ (p:ℝ) ≤ ((N:ℝ)/A)^((1:ℝ)/J) := by
    apply (eventually_all_finset E).mpr
    intro p _
    exact (((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (p:ℝ))).and
      (((tendsto_rpow_atTop hroot).comp hdiv).eventually (eventually_ge_atTop (p:ℝ)))
  filter_upwards [hcut,hscale,hfinite,auxiliary_cofactor_floor_scales,
    auxiliary_range_scales 1 hα (show β<1 by linarith),
    hdiv.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (K:ℝ)),eventually_ge_atTop (1:ℕ)] with
    N hcut hscale hfinite hfloor hrange hdiv1 hKroot hN
  intro x hx ζ hζ w hw k hk t htlo hthi
  have hn : (0:ℝ)<N := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<1) hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := hdiv1.trans hx
  have hends := auxiliary_log_bins_endpoints (show 1≤H by linarith)
    (show 0≤β by linarith) hn1 hk
  have ha := (hrange _ hends.1 hends.2).2.1
  have haQuarter : mrtPrimeLogLower H k ≤ (N:ℝ)^(1/4:ℝ) := hends.2.trans
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  obtain ⟨hm,hnorm,hnupper⟩ := hfloor _ ha haQuarter
  have hmK : K ≤ ⌊(N:ℝ)/mrtPrimeLogLower H k⌋₊ := by exact_mod_cast hKroot.trans hm
  have hcupper : (⌊(2*N:ℝ)/mrtPrimeLogLower H k⌋₊:ℝ)^(α/4) ≤ (2*(N:ℝ))^(α/4) :=
    Real.rpow_le_rpow (by positivity) hnupper hc.le
  have hrootx : ((N:ℝ)/A)^((1:ℝ)/J) ≤ x^((1:ℝ)/J) :=
    Real.rpow_le_rpow (by positivity) hx hroot.le
  apply hbound N (mrtPrimeLogLower H k) x ha hx1 hmK
    (hcupper.trans ((show (2*(N:ℝ))^(α/4)<((N:ℝ)/A)^((1:ℝ)/J) from hscale).le.trans hrootx))
    (fun p hp => (hfinite p hp).2.trans hrootx) ζ hζ _ ?_ ?_ w hw t htlo (hthi.trans hnorm)
  · intro p hp
    have hb := mrtPrimeBand_bounds (Real.rpow_nonneg hn.le α) (Real.rpow_nonneg hn.le β) hp
    refine ⟨mrtPrimeBand_prime hp,?_,?_⟩
    · exact lt_of_le_of_lt hcupper ((show (2*(N:ℝ))^(α/4)<(N:ℝ)^α by simpa using hcut).trans hb.1)
    · exact hb.2.trans ((Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : β≤1/2)).trans hm)
  · apply disjoint_left.mpr
    intro p hpE hpP
    have hb := mrtPrimeBand_bounds (Real.rpow_nonneg hn.le α) (Real.rpow_nonneg hn.le β) hpP
    exact (not_lt_of_ge (hfinite p hpE).1) hb.1

end JointDickman

end OAI
