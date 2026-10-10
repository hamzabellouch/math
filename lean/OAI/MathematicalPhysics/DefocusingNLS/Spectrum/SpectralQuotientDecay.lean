import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralQuotientJet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Outgoing columns divided by the profile satisfy the energy boundary decay criterion. -/

open Filter Asymptotics
namespace DefocusingNLS

theorem spectralQuotientJet_bigO (ν : ℂ) (Y Q : ℝ → ℂ × ℂ)
    (M K D : ℝ) (hY : ∀ t, 0 ≤ t → ‖Y t‖ ≤ M)
    (hQ : ∀ t, 0 ≤ t → ‖((Q t).1)⁻¹‖ ≤ K)
    (hQ' : ∀ t, 0 ≤ t → ‖(Q t).2‖ ≤ D) :
    (fun r => (spectralQuotientJet ν Y Q r).1) =O[atTop] (fun r : ℝ => r^ν.re) ∧
    (fun r => (spectralQuotientJet ν Y Q r).2) =O[atTop] (fun r : ℝ => r^(ν.re-1)) := by
  constructor
  · apply IsBigO.of_bound (M*K)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have ht := Real.log_nonneg hr
    have h := (spectralQuotientJet_bounds ν Y Q M K D r hr0
      (hY _ ht) (hQ _ ht) (hQ' _ ht)).1
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr0 _),mul_comm] using h
  · apply IsBigO.of_bound (((‖ν‖+1)*M)*K+M*D*K^2)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := zero_lt_one.trans_le hr
    have ht := Real.log_nonneg hr
    have h := (spectralQuotientJet_bounds ν Y Q M K D r hr0
      (hY _ ht) (hQ _ ht) (hQ' _ ht)).2
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hr0 _),mul_comm] using h

theorem spectralQuotient_energy_decay (ν : ℂ) (hν : ν.re ≤ -8)
    (Y Q : ℝ → ℂ × ℂ) (M K D : ℝ)
    (hY : ∀ t, 0 ≤ t → ‖Y t‖ ≤ M)
    (hQ : ∀ t, 0 ≤ t → ‖((Q t).1)⁻¹‖ ≤ K)
    (hQ' : ∀ t, 0 ≤ t → ‖(Q t).2‖ ≤ D)
    (hQ0 : ∀ t, 0 ≤ t → (Q t).1 ≠ 0)
    (hYd : ∀ t, 0 ≤ t → HasDerivAt (fun s => (Y s).1) (Y t).2 t)
    (hQd : ∀ t, 0 ≤ t → HasDerivAt (fun s => (Q s).1) (Q t).2 t)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z : ℂ, ‖L z‖ ≤ ‖z‖) :
    (fun r => L (spectralQuotientJet ν Y Q r).1) =O[atTop] (fun r : ℝ => r^(-8 : ℝ)) ∧
      deriv (fun r => L (spectralQuotientJet ν Y Q r).1) =O[atTop]
        (fun r : ℝ => r^(-9 : ℝ)) := by
  obtain ⟨hv,hd⟩ := spectralQuotientJet_bigO ν Y Q M K D hY hQ hQ'
  have hpow : (fun r : ℝ => r^ν.re) =O[atTop] (fun r : ℝ => r^(-8 : ℝ)) := by
    apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _)]
    exact Real.rpow_le_rpow_of_exponent_le hr hν
  have hpow' : (fun r : ℝ => r^(ν.re-1)) =O[atTop] (fun r : ℝ => r^(-9 : ℝ)) := by
    apply Eventually.isBigO
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _)]
    exact Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hLv : (fun r => L (spectralQuotientJet ν Y Q r).1) =O[atTop]
      (fun r => (spectralQuotientJet ν Y Q r).1) := by
    exact IsBigO.of_bound 1 (Eventually.of_forall fun r => by simpa only [one_mul] using hL _)
  have hLd : (fun r => L (spectralQuotientJet ν Y Q r).2) =O[atTop]
      (fun r => (spectralQuotientJet ν Y Q r).2) := by
    exact IsBigO.of_bound 1 (Eventually.of_forall fun r => by simpa only [one_mul] using hL _)
  refine ⟨hLv.trans (hv.trans hpow),?_⟩
  apply (hLd.trans (hd.trans hpow')).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have ht := Real.log_nonneg hr
  have hderiv := spectralQuotientJet_hasDerivAt ν Y Q r hr0 (hQ0 _ ht) (hYd _ ht) (hQd _ ht)
  exact (L.hasFDerivAt.comp_hasDerivAt r hderiv).deriv.symm

end DefocusingNLS

end OAI
