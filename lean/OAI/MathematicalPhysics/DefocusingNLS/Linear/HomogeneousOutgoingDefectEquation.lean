import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingRobin
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingDefectZero

namespace OAI

/-! # The outgoing Robin estimate gives the exact defect energy equation -/

open Set Filter Topology MeasureTheory

namespace DefocusingNLS

local notation "V" => ℂ × ℂ
local notation "End" => V →L[ℂ] V

private theorem radial_coefficient_split (z : ℂ) (r omega : ℝ) :
    11 / (r : ℂ) + Complex.I * omega + (r⁻¹ : ℝ) • z =
      (((11 + z.re) / r : ℝ) : ℂ) + Complex.I * (omega + z.im / r) := by
  apply Complex.ext
  all_goals
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
    ring

theorem homogeneousOutgoingDefect_damping
    (νp νm : ℂ) (hν : νp.re = νm.re) (A : End) (r : ℝ) (w : V) :
    -(homogeneousRadialDamping r + A) w =
      (-((((11 + νp.re) / r : ℝ) : ℂ) +
          Complex.I * (r / 2 + νp.im / r)) * w.1 -
          ((A - r⁻¹ • homogeneousDiagonal νp νm) w).1,
        -((((11 + νp.re) / r : ℝ) : ℂ) +
          Complex.I * (-r / 2 + νm.im / r)) * w.2 -
          ((A - r⁻¹ • homogeneousDiagonal νp νm) w).2) := by
  have hp := radial_coefficient_split νp r (r / 2)
  have hm := radial_coefficient_split νm r (-r / 2)
  rw [← hν] at hm
  apply Prod.ext
  all_goals
    simp only [homogeneousRadialDamping, homogeneousDiagonal, spectralTwoColumns_apply,
      add_apply, sub_apply, smul_apply, Prod.fst_add, Prod.snd_add,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg,
      Prod.smul_fst, Prod.smul_snd, Complex.real_smul, smul_eq_mul,
      mul_zero, add_zero, zero_add]
  · have hp' : 11 / (r : ℂ) + Complex.I * r / 2 + (r⁻¹ : ℝ) • νp =
        (((11 + νp.re) / r : ℝ) : ℂ) + Complex.I * (r / 2 + νp.im / r) := by
      convert hp using 1 <;> push_cast <;> ring
    rw [← hp']
    simp only [Complex.real_smul]
    ring
  · have hm' : 11 / (r : ℂ) - Complex.I * r / 2 + (r⁻¹ : ℝ) • νm =
        (((11 + νp.re) / r : ℝ) : ℂ) + Complex.I * (-r / 2 + νm.im / r) := by
      convert hm using 1 <;> push_cast <;> ring
    rw [← hm']
    simp only [Complex.real_smul]
    ring

theorem homogeneousOutgoingDefect_hasDerivAt
    (νp νm : ℂ) (hν : νp.re = νm.re) (A : ℝ → End) (W : ℝ → V) (r : ℝ)
    (hW : HasDerivAt W (-(homogeneousRadialDamping r + A r) (W r)) r) :
    HasDerivAt W
      (-((((11 + νp.re) / r : ℝ) : ℂ) +
          Complex.I * (r / 2 + νp.im / r)) * (W r).1 -
          ((A r - r⁻¹ • homogeneousDiagonal νp νm) (W r)).1,
        -((((11 + νp.re) / r : ℝ) : ℂ) +
          Complex.I * (-r / 2 + νm.im / r)) * (W r).2 -
          ((A r - r⁻¹ • homogeneousDiagonal νp νm) (W r)).2) r :=
  hW.congr_deriv (homogeneousOutgoingDefect_damping νp νm hν (A r) r (W r))

theorem homogeneousOutgoingDefect_eventually_zero
    (νp νm : ℂ) (hν : νp.re = νm.re) (A : ℝ → End) (W : ℝ → V)
    (f g : ℝ → ℂ) (R beta C B : ℝ) (N : ℕ)
    (hR : 0 < R) (hC : 0 < C)
    (hbeta : -6 ≤ beta - (11 + νp.re))
    (hgap : 0 < (N : ℝ) + beta - (11 + νp.re))
    (hW : ∀ r, R ≤ r → HasDerivAt W
      (-(homogeneousRadialDamping r + A r) (W r)) r)
    (hA : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ r in atTop,
      ‖A r - r⁻¹ • homogeneousDiagonal νp νm‖ ≤ M / r ^ 3)
    (hcomparison : ∀ᶠ r in atTop, r ^ (2 * beta) * homogeneousPairEnergy (W r) ≤
      C * homogeneousPairEnergy (f r, g r) + B * r ^ (-2 * (N : ℝ)))
    (hf : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖f r‖ ^ 2) (Ioi R))
    (hg : IntegrableOn (fun r => r ^ (11 : ℕ) * ‖g r‖ ^ 2) (Ioi R)) :
    ∀ᶠ r in atTop, W r = 0 := by
  obtain ⟨M, hM, hAM⟩ := hA
  obtain ⟨T, hT⟩ := eventually_atTop.mp hAM
  let S := max R T
  have hRS : R ≤ S := le_max_left _ _
  have hTS : T ≤ S := le_max_right _ _
  have hzero := homogeneousOutgoingDefect_eq_zero W
    (fun r => (A r - r⁻¹ • homogeneousDiagonal νp νm) (W r))
    (fun r => r / 2 + νp.im / r) (fun r => -r / 2 + νm.im / r)
    f g S (11 + νp.re) M beta C B N (hR.trans_le hRS) hM hC hbeta hgap
    (fun r hr => by
      simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_ofNat] using
        homogeneousOutgoingDefect_hasDerivAt νp νm hν A W r (hW r (hRS.trans hr)))
    (fun r hr => (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hT r (hTS.trans hr)) (norm_nonneg _)))
    hcomparison (hf.mono_set (Ioi_subset_Ioi hRS)) (hg.mono_set (Ioi_subset_Ioi hRS))
  exact (eventually_ge_atTop S).mono hzero

end DefocusingNLS

end OAI
