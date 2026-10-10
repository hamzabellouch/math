import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryPowerSeparation
import OAI.NumberTheory.JointDickman.Analysis.CharacterCofactorWindow
import OAI.NumberTheory.JointDickman.Amplification.TwistedBinInterpolants

namespace OAI

/-! # Nonprincipal bin cofactors throughout the auxiliary power band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem twisted_auxiliary_cofactor {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
    (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
    (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
        (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
          (finitePrimeWeight E w) a χ) N (mrtPrimeLogLower H k) t‖ ≤ ε := by
  have hc : 0 < α/4 := by positivity
  have hc1 : α/4 ≤ 1 := by linarith
  have hroot : 0 < (1:ℝ)/J := by positivity
  obtain ⟨K,_hK,hbound⟩ := character_count_window χ hχ hc hc1 E hε
  have hdiv : Tendsto (fun N : ℕ => (N:ℝ)/A) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hA
  have hscale := (eventually_scaled_power_lt (show α/4<(1:ℝ)/J by linarith)
    (by norm_num : (0:ℝ)<2) hA).filter_mono tendsto_natCast_atTop_atTop
  filter_upwards [hscale,auxiliary_cofactor_floor_scales,
    auxiliary_range_scales 1 hα (show β<1 by linarith),
    hdiv.eventually (eventually_ge_atTop 1),
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (K:ℝ)),eventually_ge_atTop (1:ℕ)] with
    N hscale hfloor hrange hdiv1 hKroot hN
  intro x hx m a w hw k hk t ht
  let F := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight E w) a χ
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
  have hmult : F.IsMultiplicative := twistedWeightedBinInterpolant_multiplicative _ _
    (finitePrimeWeight_multiplicative hE w) a χ
  have hnormF : ∀ n, ‖F n‖ ≤ 1 := by
    intro n
    apply twistedWeightedBinInterpolant_norm_le _ _ _ a χ n
    intro v
    rw [abs_of_nonneg (finitePrimeWeight_bounds hw v).1]
    exact (finitePrimeWeight_bounds hw v).2
  have heq : ∀ p : ℕ, p.Prime → p ∉ E →
      (p:ℝ) ≤ (⌊(2*N:ℝ)/mrtPrimeLogLower H k⌋₊:ℝ)^(α/4) → F p=χ p := by
    intro p hp hpE hpc
    apply twistedWeightedBinInterpolant_small_prime hJ j hj hE w a χ hx1 hp hpE
    exact hpc.trans (hcupper.trans ((show (2*(N:ℝ))^(α/4)<((N:ℝ)/A)^((1:ℝ)/J)
      from hscale).le.trans hrootx))
  have hh := hbound N (mrtPrimeLogLower H k) ha hmK F hmult hnormF heq
    ∅ (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)) (by simp)
    (fun _ hp => mrtPrimeBand_prime hp) t (ht.trans hnorm)
  have hempty : mrtMissingCoefficient F ∅=(F : ℕ → ℂ) := by
    funext n
    simp [mrtMissingCoefficient,mrtPrimeMask,mrtPrimeAvoids]
  rwa [hempty] at hh

end JointDickman

end OAI
