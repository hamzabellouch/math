import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingDilation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousAnnulusBounds

namespace OAI

/-! # Uniform sampling of physical symbol annuli

The Fourier sample of a physical radius-R annulus has norm O(R^(-a)),
uniformly for L ≥ R.  The constant uses finitely many symbol derivatives.
-/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def schwartzPhysicalDilation (a R : ℝ) (hR : 0 < R) :
    𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ((R ^ (-2 * a) : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      ((Units.mk0 R⁻¹ (inv_ne_zero hR.ne')) • ContinuousLinearEquiv.refl ℝ E)

@[simp] theorem schwartzPhysicalDilation_apply (a R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) (y : E) :
    schwartzPhysicalDilation a R hR ψ y =
      (R ^ (-2 * a) : ℝ) * ψ (R⁻¹ • y) := by
  simp [schwartzPhysicalDilation]

theorem radianFourierKernel_schwartzPhysicalDilation (a R : ℝ) (hR : 0 < R)
    (ψ : 𝓢(E, ℂ)) :
    radianFourierKernel (schwartzPhysicalDilation a R hR ψ) =
      homogeneousFourierDilation a R hR (radianFourierKernel ψ) := by
  ext ξ
  rw [radianFourierKernel_apply, homogeneousFourierDilation_apply,
    radianFourierKernel_apply]
  have hf : (schwartzPhysicalDilation a R hR ψ : E → ℂ) =
      ((R ^ (-2 * a) : ℝ) : ℂ) • (fun y => ψ (R⁻¹ • y)) := by
    funext y
    exact schwartzPhysicalDilation_apply a R hR ψ y
  rw [hf, radianFourierIntegral_smul, Pi.smul_apply, radianFourier_dilation R hR]
  have hp : R ^ (-2 * a) * R ^ (12 : ℕ) = R ^ (12 - 2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    norm_num
    ring
  simp only [Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, hp]

theorem schwartzPhysicalDilation_annulus (a R : ℝ) (hR : 0 < R)
    (κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    schwartzPhysicalDilation a R hR
        (homogeneousAnnulusPiece a R κ hκ Q hQ) y = κ (R⁻¹ • y) * Q y := by
  rw [schwartzPhysicalDilation_apply]
  exact homogeneousAnnulusPiece_rescale a R hR κ hκ Q hQ y

theorem exists_schwartzAnnulusSample_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (κ : 𝓢(E, ℂ)) (hκ : HasCompactSupport (κ : E → ℂ))
    (hκann : ∀ x ∈ tsupport (κ : E → ℂ), (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
      (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∀ (R L : ℝ) (hR : 1 ≤ R) (hRL : R ≤ L),
        ‖schwartzTorusSample a k L ha1 hk (hR.trans hRL)
          (radianFourierKernel (schwartzPhysicalDilation a R (by linarith)
            (homogeneousAnnulusPiece a R κ hκ Q hQ)))‖ ≤ C * D * R ^ (-a) := by
  obtain ⟨N, C, hC, hbound⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  refine ⟨N, C * homogeneousAnnulusJetConstant a κ N, by
    exact mul_nonneg hC (homogeneousAnnulusJetConstant_nonneg a κ N), ?_⟩
  intro Q hQ D hD hsymbol R L hR hRL
  have hRp : 0 < R := by linarith
  have hLR : 1 ≤ L / R := (le_div_iff₀ hRp).mpr (by simpa using hRL)
  have hj := hbound (homogeneousAnnulusPiece a R κ hκ Q hQ)
    (homogeneousAnnulusJetConstant a κ N * D)
    (mul_nonneg (homogeneousAnnulusJetConstant_nonneg a κ N) hD)
    (fun n hn x => homogeneousAnnulusPiece_jet_bound a R D ha hRp hD κ hκ hκann
      Q hQ N hsymbol n hn x) (L / R) hLR
  rw [radianFourierKernel_schwartzPhysicalDilation]
  exact (schwartzTorusSample_homogeneousDilation_norm_le a k R L ha ha1 hk hR hRL
    (radianFourierKernel (homogeneousAnnulusPiece a R κ hκ Q hQ))).trans
      ((mul_le_mul_of_nonneg_left hj (Real.rpow_nonneg hRp.le _)).trans_eq (by ring))

end DefocusingNLS

end OAI
