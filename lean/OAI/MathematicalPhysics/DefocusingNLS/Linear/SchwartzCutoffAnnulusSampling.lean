import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzScaledCutoff

namespace OAI

/-! # Uniform samples of cutoff profile annuli

This combines actual symbol jets, a cutoff varying at scale L, and the exact
radius-R sampling law.  All constants are independent of 1 ≤ R ≤ L.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cutoffProfileAnnulus (a R L : ℝ) (χ κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    𝓢(E, ℂ) :=
  schwartzScaledCutoff (R / L) χ (homogeneousAnnulusPiece a R κ hκ Q hQ)
    (hκ.mul_right (f' := normalizedPhysicalProfile a R Q))

theorem cutoffProfileAnnulus_physical (a R L : ℝ) (hR : 0 < R) (hL : 0 < L)
    (χ κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    schwartzPhysicalDilation a R hR (cutoffProfileAnnulus a R L χ κ hκ Q hQ) y =
      κ (R⁻¹ • y) * Q y * χ (L⁻¹ • y) := by
  have harg : (R / L) • (R⁻¹ • y) = L⁻¹ • y := by
    rw [smul_smul]
    congr 1
    field_simp
  rw [schwartzPhysicalDilation_apply]
  change (R ^ (-2 * a) : ℝ) *
    (homogeneousAnnulusPiece a R κ hκ Q hQ (R⁻¹ • y) *
      χ ((R / L) • (R⁻¹ • y))) = _
  rw [harg, ← mul_assoc, homogeneousAnnulusPiece_rescale a R hR]

theorem exists_cutoffProfileAnnulus_sampling_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (R L : ℝ) (hR : 1 ≤ R) (hRL : R ≤ L),
        ‖schwartzTorusSample a k L ha1 hk (hR.trans hRL)
          (radianFourierKernel (schwartzPhysicalDilation a R (by linarith)
            (cutoffProfileAnnulus a R L χ κ hκ Q hQ)))‖ ≤ C * D * R ^ (-a) := by
  obtain ⟨N, C, hC, hbound⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  refine ⟨N, C * schwartzCutoffJetConstant χ N * homogeneousAnnulusJetConstant a κ N,
    mul_nonneg (mul_nonneg hC (schwartzCutoffJetConstant_nonneg χ N))
      (homogeneousAnnulusJetConstant_nonneg a κ N), ?_⟩
  intro Q hQ D hD hsymbol R L hR hRL
  have hRp : 0 < R := by linarith
  have hLp : 0 < L := by linarith
  have hLR : 1 ≤ L / R := (le_div_iff₀ hRp).mpr (by simpa using hRL)
  have hδp : 0 < R / L := div_pos hRp hLp
  have hδ1 : R / L ≤ 1 := (div_le_one hLp).mpr hRL
  have hjet : ∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N *
      ‖iteratedFDeriv ℝ n (cutoffProfileAnnulus a R L χ κ hκ Q hQ) x‖ ≤
        schwartzCutoffJetConstant χ N * (homogeneousAnnulusJetConstant a κ N * D) := by
    intro n hn x
    exact schwartzScaledCutoff_jet_bound (R / L) (homogeneousAnnulusJetConstant a κ N * D)
      hδp hδ1 (mul_nonneg (homogeneousAnnulusJetConstant_nonneg a κ N) hD)
      χ (homogeneousAnnulusPiece a R κ hκ Q hQ)
      (hκ.mul_right (f' := normalizedPhysicalProfile a R Q)) N
      (fun n hn x => homogeneousAnnulusPiece_jet_bound a R D ha hRp hD κ hκ hκann
        Q hQ N hsymbol n hn x) n hn x
  have hj := hbound (cutoffProfileAnnulus a R L χ κ hκ Q hQ)
    (schwartzCutoffJetConstant χ N * (homogeneousAnnulusJetConstant a κ N * D))
    (mul_nonneg (schwartzCutoffJetConstant_nonneg χ N)
      (mul_nonneg (homogeneousAnnulusJetConstant_nonneg a κ N) hD))
    hjet (L / R) hLR
  rw [radianFourierKernel_schwartzPhysicalDilation]
  exact (schwartzTorusSample_homogeneousDilation_norm_le a k R L ha ha1 hk hR hRL
    (radianFourierKernel (cutoffProfileAnnulus a R L χ κ hκ Q hQ))).trans
      ((mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hRp.le _)).trans_eq (by ring))

end DefocusingNLS

end OAI
