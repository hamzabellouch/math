import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzDilationJets
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzCutoffAnnulusSampling

namespace OAI

/-! # The outer annulus in the uniform cutoff estimate

The radius-R annulus with L ≤ R ≤ 2L is reduced to a bounded dilation at
effective period one.  This covers the final annulus in a dyadic decomposition.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_outerSchwartzDilation_sampling_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (ψ : 𝓢(E, ℂ)) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ ≤ D) →
      ∀ (L R : ℝ) (hL : 1 ≤ L) (hLR : L ≤ R), R ≤ 2 * L →
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (schwartzPhysicalDilation a R (by linarith) ψ))‖ ≤ C * D * L ^ (-a) := by
  obtain ⟨N, C, hC, hb⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  refine ⟨N, C * 2 ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro ψ D hD hjet L R hL hLR hR2L
  have hLp : 0 < L := by linarith
  have hRp : 0 < R := by linarith
  let σ := R / L
  have hσ : 1 ≤ σ := (le_div_iff₀ hLp).mpr (by simpa using hLR)
  have hσp : 0 < σ := by linarith
  have hσ2 : σ ≤ 2 := (div_le_iff₀ hLp).mpr hR2L
  let φ := schwartzPhysicalDilation a σ hσp ψ
  have hφ : ‖schwartzTorusSample a k 1 ha1 hk le_rfl (radianFourierKernel φ)‖ ≤
      C * (2 ^ N * D) :=
    hb φ (2 ^ N * D) (by positivity)
      (fun n hn x => schwartzPhysicalDilation_boundedRatio_jets a σ D ha hσ hσ2 hD
        ψ N hjet n hn x) 1 le_rfl
  have he : schwartzPhysicalDilation a R hRp ψ =
      schwartzPhysicalDilation a L hLp φ := by
    dsimp only [φ]
    rw [schwartzPhysicalDilation_comp]
    have hRσ : L * σ = R := by dsimp [σ]; field_simp
    simp only [hRσ]
  rw [he, radianFourierKernel_schwartzPhysicalDilation]
  have hs := schwartzTorusSample_homogeneousDilation_norm_le a k L L ha ha1 hk hL le_rfl
    (radianFourierKernel φ)
  simp only [div_self hLp.ne'] at hs
  exact hs.trans ((mul_le_mul_of_nonneg_left hφ (Real.rpow_nonneg hLp.le _)).trans_eq
    (by ring))

noncomputable def schwartzDoubleScale (χ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((Units.mk0 (2 : ℝ) (by norm_num)) • ContinuousLinearEquiv.refl ℝ E) χ

@[simp] theorem schwartzDoubleScale_apply (χ : 𝓢(E, ℂ)) (x : E) :
    schwartzDoubleScale χ x = χ ((2 : ℝ) • x) := by simp [schwartzDoubleScale]

theorem cutoffProfileAnnulus_outer_rescale (a R L : ℝ) (χ κ : 𝓢(E, ℂ))
    (hκ : HasCompactSupport (κ : E → ℂ)) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    cutoffProfileAnnulus a R L χ κ hκ Q hQ =
      schwartzScaledCutoff (R / (2 * L)) (schwartzDoubleScale χ)
        (homogeneousAnnulusPiece a R κ hκ Q hQ)
        (hκ.mul_right (f' := normalizedPhysicalProfile a R Q)) := by
  ext x
  change homogeneousAnnulusPiece a R κ hκ Q hQ x * χ ((R / L) • x) =
    homogeneousAnnulusPiece a R κ hκ Q hQ x *
      schwartzDoubleScale χ ((R / (2 * L)) • x)
  rw [schwartzDoubleScale_apply, smul_smul]
  have he : (2 : ℝ) * (R / (2 * L)) = R / L := by ring
  rw [he]

theorem exists_outerCutoffAnnulus_sampling_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (L R : ℝ) (hL : 1 ≤ L) (hLR : L ≤ R), R ≤ 2 * L →
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (schwartzPhysicalDilation a R (by linarith)
            (cutoffProfileAnnulus a R L χ κ hκ Q hQ)))‖ ≤ C * D * L ^ (-a) := by
  obtain ⟨N, C, hC, hb⟩ := exists_outerSchwartzDilation_sampling_bound a k ha ha1 hk
  let B := schwartzCutoffJetConstant (schwartzDoubleScale χ) N
  let A := homogeneousAnnulusJetConstant a κ N
  have hB : 0 ≤ B := schwartzCutoffJetConstant_nonneg _ _
  have hA : 0 ≤ A := homogeneousAnnulusJetConstant_nonneg _ _ _
  refine ⟨N, C * B * A, mul_nonneg (mul_nonneg hC hB) hA, ?_⟩
  intro Q hQ D hD hsymbol L R hL hLR hR2L
  have hLp : 0 < L := by linarith
  have hRp : 0 < R := by linarith
  have hδp : 0 < R / (2 * L) := by positivity
  have hδ1 : R / (2 * L) ≤ 1 := (div_le_one (by positivity)).mpr hR2L
  have hjet : ∀ n ≤ N, ∀ x : E, (1 + ‖x‖) ^ N *
      ‖iteratedFDeriv ℝ n (cutoffProfileAnnulus a R L χ κ hκ Q hQ) x‖ ≤ B * (A * D) := by
    intro n hn x
    rw [cutoffProfileAnnulus_outer_rescale]
    exact schwartzScaledCutoff_jet_bound (R / (2 * L)) (A * D) hδp hδ1
      (mul_nonneg hA hD) (schwartzDoubleScale χ)
      (homogeneousAnnulusPiece a R κ hκ Q hQ)
      (hκ.mul_right (f' := normalizedPhysicalProfile a R Q)) N
      (fun n hn x => homogeneousAnnulusPiece_jet_bound a R D ha hRp hD κ hκ hκann
        Q hQ N hsymbol n hn x) n hn x
  exact (hb (cutoffProfileAnnulus a R L χ κ hκ Q hQ) (B * (A * D))
    (mul_nonneg hB (mul_nonneg hA hD)) hjet L R hL hLR hR2L).trans_eq (by ring)

end DefocusingNLS

end OAI
