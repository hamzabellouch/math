import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProfileSampling
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualSampling

namespace OAI

/-! The constructed profile supplies the concrete uniform cutoff and residual bounds. -/

open Set
open scoped ContDiff SchwartzMap
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialShootingA_bounds (n : ℕ) (w : RadialShootingDisk) :
    0 < radialShootingA n ∧ radialShootingA n < 1 := by
  have hp := radialShootingInner_power_pos n w
  have hn : (1 : ℝ) ≤ ((n+radialInnerShootingThreshold : ℕ) : ℝ) := by exact_mod_cast hp
  unfold radialShootingA
  constructor
  · exact one_div_pos.mpr (by linarith)
  · exact (div_lt_one (by linarith)).mpr (by linarith)

theorem radialMatchedCartesian_global_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) y‖ ≤
        D*‖y‖^(-2*radialShootingA n-(j : ℝ)) := by
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_symbol n z hX hz j
  have hQ := radialMatchedCartesian_contDiff n z hX hz
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    ((hQ.of_le (by simp : (j : ℕ∞ω) ≤ ∞)).continuous_iteratedFDeriv'.continuousOn)
  refine ⟨max C D,hD.trans (le_max_right _ _),?_⟩
  intro y hy
  by_cases hlarge : 1 ≤ ‖y‖
  · exact (hb y hlarge).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  · have hsmall : ‖y‖ ≤ 1 := (lt_of_not_ge hlarge).le
    have hcore : ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) y‖ ≤ max C D :=
      (hC y (by simpa only [Metric.mem_closedBall,dist_zero_right] using hsmall)).trans
        (le_max_left _ _)
    have hneg : -2*radialShootingA n-(j : ℝ) ≤ 0 := by
      have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
      linarith
    have hp : 1 ≤ ‖y‖^(-2*radialShootingA n-(j : ℝ)) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.mpr hy) hsmall hneg
    exact hcore.trans (le_mul_of_one_le_right (hD.trans (le_max_right _ _)) hp)

theorem radialMatchedCartesian_finite_symbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j ≤ N, ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ j (radialMatchedCartesian n z) y‖ ≤
        D*‖y‖^(-2*radialShootingA n-(j : ℝ)) := by
  choose D hD hb using radialMatchedCartesian_global_symbol n z hX hz
  refine ⟨∑ j ∈ Finset.range (N+1), D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro j hj y hy
  exact (hb j y hy).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_range.mpr (by omega)))
    (Real.rpow_nonneg (norm_nonneg _) _))

theorem radialMatchedCutoff_sampling_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y=0) :
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
      ‖schwartzTorusSample (radialShootingA n) k L ha1 hk hL (radianFourierKernel
        (cutoffProfileSchwartz L (by linarith) χ hχ (radialMatchedCartesian n z) hQ))‖ ≤ C := by
  intro ha1 hQ
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  obtain ⟨N,hN⟩ := exists_cutoffProfile_sampling_bound (radialShootingA n) k ha ha1 hk χ hχ hχzero
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_finite_symbol n z hX hz N
  exact hN _ hQ D hD hb

theorem radialMatchedResidual_sampling_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ y : E, ‖y‖ < 1/2 → χ y=1)
    (hχzero : ∀ y : E, 2 < ‖y‖ → χ y=0) :
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let hQ := radialMatchedCartesian_contDiff n z hX hz
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
      ‖schwartzTorusSample (radialShootingA n) k L ha1 hk hL (radianFourierKernel
        (cutoffResidualSchwartz χ hχ hχone hχzero (radialShootingA n) L
          (lt_of_lt_of_le zero_lt_one hL) (n+radialInnerShootingThreshold)
          (radialMatchedCartesian n z) hQ))‖ ≤ C*L^(-2-radialShootingA n) := by
  intro ha1 hQ
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  obtain ⟨N,hN⟩ := exists_cutoffResidual_sampling_bound (radialShootingA n) k ha ha1 hk
    (n+radialInnerShootingThreshold) χ hχ hχone hχzero
  obtain ⟨D,hD,hb⟩ := radialMatchedCartesian_finite_symbol n z hX hz N
  exact hN _ hQ D hD hb

end DefocusingNLS

end OAI
