import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularCoupling
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousOutgoingPropagation

namespace OAI

/-! Small-ball uniqueness for the actual physical radial system. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousRegular_state_velocity (νp νm eta : ℂ) (m : ℕ) (Q : ℝ → ℂ)
    (U : ℝ → E₄) (r : ℝ)
    (hU : HasDerivAt U (spectralPhysicalCircularField νp νm eta m (Q r) r (U r)) r) :
    deriv (fun s => (U s).1.1) r = (U r).1.2 ∧
      deriv (fun s => (U s).2.1) r = (U r).2.2 := by
  have hp := ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
    (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ))).hasFDerivAt.comp_hasDerivAt r hU
  have hm := ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp
    (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ))).hasFDerivAt.comp_hasDerivAt r hU
  exact ⟨hp.deriv, hm.deriv⟩

theorem homogeneousRegular_state_equation (νp νm : ℂ) (eta : ℝ) (m : ℕ)
    (Q : ℝ → ℂ) (U : ℝ → E₄) (R : ℝ)
    (hU : ∀ r ∈ Ioc 0 R, HasDerivAt U
      (spectralPhysicalCircularField νp νm (eta : ℂ) m (Q r) r (U r)) r)
    (r : ℝ) (hr : r ∈ Ioo 0 R) :
    let F := fun s => (U s).1.1
    let G := fun s => (U s).2.1
    (deriv (deriv F) r + ((11 / r : ℝ) : ℂ) * deriv F r -
      ((eta / r ^ 2 : ℝ) : ℂ) * F r = -Complex.I * (r / 2 : ℝ) * deriv F r +
        (spectralDiagonalCoefficient m (Q r) + Complex.I * νp / 2) * F r +
        spectralCrossCoefficient m (Q r) * G r) ∧
    (deriv (deriv G) r + ((11 / r : ℝ) : ℂ) * deriv G r -
      ((eta / r ^ 2 : ℝ) : ℂ) * G r = Complex.I * (r / 2 : ℝ) * deriv G r +
        (star (spectralDiagonalCoefficient m (Q r)) - Complex.I * νm / 2) * G r +
        star (spectralCrossCoefficient m (Q r)) * F r) := by
  let F := fun s => (U s).1.1
  let G := fun s => (U s).2.1
  have hv (s : ℝ) (hs : s ∈ Ioc 0 R) :=
    homogeneousRegular_state_velocity νp νm (eta : ℂ) m Q U s (hU s hs)
  have hFp : deriv F =ᶠ[nhds r] (fun s => (U s).1.2) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    exact (hv s ⟨hs.1, hs.2.le⟩).1
  have hGp : deriv G =ᶠ[nhds r] (fun s => (U s).2.2) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    exact (hv s ⟨hs.1, hs.2.le⟩).2
  have hp := (((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
    (ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ))).hasFDerivAt.comp_hasDerivAt r
      (hU r ⟨hr.1, hr.2.le⟩)).congr_of_eventuallyEq hFp
  have hm := (((ContinuousLinearMap.snd ℝ ℂ ℂ).comp
    (ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ))).hasFDerivAt.comp_hasDerivAt r
      (hU r ⟨hr.1, hr.2.le⟩)).congr_of_eventuallyEq hGp
  change (_ = _) ∧ (_ = _)
  dsimp only [F, G]
  rw [hp.deriv, hm.deriv, (hv r ⟨hr.1, hr.2.le⟩).1, (hv r ⟨hr.1, hr.2.le⟩).2]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']
  constructor <;> dsimp only [spectralPhysicalCircularField]
  all_goals push_cast; ring

theorem homogeneousRegular_physical_small_ball (νp νm : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (hQ : Continuous Q) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (R eta : ℝ), 0 < R → R ≤ δ → 0 ≤ eta →
      ∀ F G : ℝ → ℂ, ContDiff ℝ 2 F → ContDiff ℝ 2 G → F R = 0 → G R = 0 →
      (∀ r, 0 < r → r ≤ R → deriv (deriv F) r + ((11 / r : ℝ) : ℂ) * deriv F r -
        ((eta / r ^ 2 : ℝ) : ℂ) * F r = -Complex.I * (r / 2 : ℝ) * deriv F r +
          (spectralDiagonalCoefficient m (Q r) + Complex.I * νp / 2) * F r +
          spectralCrossCoefficient m (Q r) * G r) →
      (∀ r, 0 < r → r ≤ R → deriv (deriv G) r + ((11 / r : ℝ) : ℂ) * deriv G r -
        ((eta / r ^ 2 : ℝ) : ℂ) * G r = Complex.I * (r / 2 : ℝ) * deriv G r +
          (star (spectralDiagonalCoefficient m (Q r)) - Complex.I * νm / 2) * G r +
          star (spectralCrossCoefficient m (Q r)) * F r) →
      ∀ r ∈ Icc 0 R, F r = 0 ∧ G r = 0 := by
  let A := fun r => spectralDiagonalCoefficient m (Q r) + Complex.I * νp / 2
  let B := fun r => spectralCrossCoefficient m (Q r)
  let C := fun r => star (spectralDiagonalCoefficient m (Q r)) - Complex.I * νm / 2
  let D := fun r => star (spectralCrossCoefficient m (Q r))
  have hA : Continuous A := by dsimp [A, spectralDiagonalCoefficient]; fun_prop
  have hB : Continuous B := by dsimp [B, spectralCrossCoefficient]; fun_prop
  have hC : Continuous C := by dsimp [C, spectralDiagonalCoefficient]; fun_prop
  have hD : Continuous D := by dsimp [D, spectralCrossCoefficient]; fun_prop
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    ((hA.prodMk hB).prodMk (hC.prodMk hD)).continuousOn
  let K := max M 0
  have hK : 0 ≤ K := le_max_right _ _
  have hcoeff (r : ℝ) (hr : r ∈ Icc 0 1) :
      ‖A r‖ ≤ K ∧ ‖B r‖ ≤ K ∧ ‖C r‖ ≤ K ∧ ‖D r‖ ≤ K := by
    have hb : ‖((A r, B r), (C r, D r))‖ ≤ K := (hM r hr).trans (le_max_left _ _)
    exact ⟨((norm_fst_le _).trans (norm_fst_le _)).trans hb,
      ((norm_snd_le _).trans (norm_fst_le _)).trans hb,
      ((norm_fst_le _).trans (norm_snd_le _)).trans hb,
      ((norm_snd_le _).trans (norm_snd_le _)).trans hb⟩
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 8) (2 * K + 1)
  let δ := min 1 ε
  have hδ : 0 < δ := lt_min zero_lt_one hε
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  intro R eta hR hRδ heta F G hF hG hFR hGR hODEF hODEG
  have hR1 : R ≤ 1 := hRδ.trans (min_le_left _ _)
  have hRsqR : R ^ 2 ≤ R := by nlinarith
  have hRsq : R ^ 2 ≤ ε := hRsqR.trans (hRδ.trans (min_le_right _ _))
  exact homogeneousRegular_coupled_zero R eta K hR hR1 heta hK
    ((mul_le_mul_of_nonneg_left hRsq (by positivity)).trans_lt hεsmall)
    A B C D F G hA hB hC hD hF hG hFR hGR
    (fun r hr => hcoeff r ⟨hr.1, hr.2.trans hR1⟩) hODEF hODEG

end DefocusingNLS

end OAI
