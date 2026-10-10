import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRegularPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingGluing

namespace OAI

/-! Regularity of a physical state obtained by matching two ODE branches. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem homogeneousGlued_state_smooth (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (hQ : ContDiffOn ℝ ∞ Q (Ioi 0)) (U : ℝ → E₄)
    (hU : ∀ r, 0 < r → HasDerivAt U
      (spectralPhysicalCircularField νp νm eta m (Q r) r (U r)) r) :
    ContDiffOn ℝ ∞ U (Ioi 0) := by
  intro r hr
  have hr0 : 0 < r := hr
  have hsub : Icc (r / 2) (r + 1) ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact (half_pos hr0).trans_le ht.1
  have hs : ContDiffOn ℝ ∞ U (Icc (r / 2) (r + 1)) := by
    apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun t V => spectralPhysicalCircularField νp νm eta m (Q t) t V)
      (u := (univ : Set E₄))
    · exact spectralPhysicalCircularField_contDiffOn νp νm eta m Q _
        (hQ.mono hsub) (fun t ht => (hsub ht).ne')
    · exact fun t ht => (hU t (hsub ht)).hasDerivWithinAt
    · exact fun _ _ => mem_univ _
  exact (hs.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))).contDiffWithinAt

theorem homogeneousGlued_positions_c2 (νp νm eta : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (hQ : ContDiffOn ℝ ∞ Q (Ioi 0))
    (U F : ℝ → E₄) (R : ℝ) (hR : 0 < R)
    (hF : ContDiff ℝ 2 (fun r => (F r).1.1) ∧
      ContDiff ℝ 2 (fun r => (F r).2.1))
    (hUF : ∀ r, r < R → U r = F r)
    (hU : ∀ r, 0 < r → HasDerivAt U
      (spectralPhysicalCircularField νp νm eta m (Q r) r (U r)) r) :
    ContDiff ℝ 2 (fun r => (U r).1.1) ∧
      ContDiff ℝ 2 (fun r => (U r).2.1) := by
  have hs := homogeneousGlued_state_smooth νp νm eta m Q hQ U hU
  constructor
  · rw [contDiff_iff_contDiffAt]
    intro r
    by_cases hr : 0 < r
    · exact ((hs.fst.fst r hr).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)
    · apply (hF.1.contDiffAt).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt hr) hR)] with t ht
      exact congrArg (fun V : E₄ => V.1.1) (hUF t ht)
  · rw [contDiff_iff_contDiffAt]
    intro r
    by_cases hr : 0 < r
    · exact ((hs.snd.fst r hr).contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)
    · apply (hF.2.contDiffAt).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt (le_of_not_gt hr) hR)] with t ht
      exact congrArg (fun V : E₄ => V.2.1) (hUF t ht)

theorem homogeneousGlued_eigenpair (a b : ℝ) (eta : ℝ) (lam : ℂ) (m : ℕ)
    (Q : ℝ → ℂ) (U : ℝ → E₄)
    (hU : ∀ r, 0 < r → HasDerivAt U
      (spectralPhysicalCircularField (-2 * (a : ℂ) + 2 * Complex.I * (b : ℂ) - 2 * lam)
        (-2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) - 2 * lam)
        (eta : ℂ) m (Q r) r (U r)) r) :
    IsHarmonicRadialEigenpair a b m Q (eta : ℂ) lam
      (fun r => (U r).1.1) (fun r => (U r).2.1) := by
  intro r hr
  obtain ⟨hp, hm⟩ := homogeneousRegular_state_equation
    (-2 * (a : ℂ) + 2 * Complex.I * (b : ℂ) - 2 * lam)
    (-2 * (a : ℂ) - 2 * Complex.I * (b : ℂ) - 2 * lam)
    eta m Q U (r + 1) (fun t ht => hU t ht.1) r ⟨hr, by linarith⟩
  dsimp only at hp hm
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, Complex.I_sq, neg_one_mul]
  constructor
  · dsimp only [spectralDiagonalCoefficient, spectralCrossCoefficient] at hp
    push_cast at hp ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq, hI3]; ring)) -Complex.I * hp
  · dsimp only [spectralDiagonalCoefficient, spectralCrossCoefficient] at hm
    push_cast at hm ⊢
    linear_combination (norm := (ring_nf; simp only [Complex.I_sq, hI3]; ring)) Complex.I * hm

end DefocusingNLS

end OAI
