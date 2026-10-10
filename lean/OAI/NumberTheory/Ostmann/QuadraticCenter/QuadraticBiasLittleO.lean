import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasBandSelection
import OAI.NumberTheory.Ostmann.QuadraticCenter.NoBiasedPrimeBlock
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticBiasLittleOWeights

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

theorem eventually_quadraticBadBandMass_le (d : Decomposition) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) :
    ∀ᶠ T : ℝ in atTop, quadraticBadBandMass d δ T ≤ ρ*T := by
  filter_upwards [eventually_bad_band_oriented_dyadic d hδ hρ,
    eventually_no_biased_prime_block d (ρ/20) δ (by positivity) hδ] with T hselect hno
  apply le_of_not_gt
  intro hm
  obtain ⟨j,G,ε,t,hlo,hhi,hcard,hG⟩ := hselect hm
  exact hno (2^j) hlo hhi G (fun p hp => (hG p hp).1)
    (fun p hp => (hG p hp).1.odd_of_ne_two (hG p hp).2.1)
    (fun p hp => ⟨(hG p hp).2.2.1,(hG p hp).2.2.2.1⟩) hcard ε t
    (fun p hp => (hG p hp).2.2.2.2)

def quadraticLogBandMass (d : Decomposition) (T : ℝ) : ℝ :=
  ∑ p ∈ closedLogarithmicPrimeBand T, (Real.log p/p)*quadraticBiasValue d p

lemma quadraticLogBandMass_nonneg (d : Decomposition) (T : ℝ) :
    0 ≤ quadraticLogBandMass d T := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_closedLogarithmicPrimeBand.mp hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le))
    (Nat.cast_nonneg _)) (quadraticBiasValue_nonneg d p)

theorem eventually_quadraticLogBandMass_le (d : Decomposition) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, quadraticLogBandMass d T ≤ ε*T := by
  filter_upwards [eventually_quadraticBadBandMass_le d
    (show 0 < ε/6 by positivity) (show 0 < ε/2 by positivity),
    eventually_closed_band_weight_le, eventually_parameter_cutoff,
    eventually_gt_atTop (Real.log 2)] with T hbad hweight hcut hT
  have hs := closed_band_bias_le_threshold d (show 0 ≤ ε/6 by positivity) hT hcut
  have hw := mul_le_mul_of_nonneg_left hweight (show 0 ≤ ε/6 by positivity)
  unfold quadraticLogBandMass
  linarith

theorem eventually_quadratic_prime_band_le (d : Decomposition) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, T ≤ Real.log p ∧ Real.log p ≤ 2*T) →
      (∑ p ∈ P, (Real.log p/p)*quadraticBiasValue d p) ≤ ε*T := by
  filter_upwards [eventually_quadraticLogBandMass_le d hε] with T hT
  intro P hprime hP
  apply le_trans _ hT
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (fun p hp => mem_closedLogarithmicPrimeBand.mpr ⟨hprime p hp,hP p hp⟩)
  intro p hp hnot
  have hpr := (mem_closedLogarithmicPrimeBand.mp hp).1
  exact mul_nonneg (div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_le))
    (Nat.cast_nonneg _)) (quadraticBiasValue_nonneg d p)

theorem quadraticLogBandMass_isLittleO (d : Decomposition) :
    quadraticLogBandMass d =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [eventually_quadraticLogBandMass_le d hε, eventually_ge_atTop (0 : ℝ)]
    with T hT hnonneg
  simpa only [Real.norm_eq_abs,abs_of_nonneg (quadraticLogBandMass_nonneg d T),
    abs_of_nonneg hnonneg] using hT

end Ostmann.QuadraticCenter

end

end OAI
