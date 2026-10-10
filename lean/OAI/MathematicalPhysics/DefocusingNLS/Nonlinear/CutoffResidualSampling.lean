import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualJets
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzAnnulusSampling

namespace OAI

/-! # The exact cutoff residual has expanding-torus norm O(L^(-2-a)) -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cutoffResidualSchwartz (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (a L : ℝ) (hL : 0 < L) (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : 𝓢(E, ℂ) :=
  ((L ^ (-2 : ℝ) : ℝ) : ℂ) • schwartzPhysicalDilation a L hL
    (normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L m Q hQ)

theorem cutoffResidualSchwartz_apply (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (a L : ℝ) (hL : 0 < L) (m : ℕ) (ha : 2 * a * (m : ℝ) = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (y : E) :
    cutoffResidualSchwartz χ hχ hχone hχzero a L hL m Q hQ y =
      cutoffResidual m L χ Q y := by
  have harg : L • (L⁻¹ • y) = y := by rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hs := cutoffResidual_scaling a L m hL ha χ Q (L⁻¹ • y)
  rw [harg] at hs
  rw [cutoffResidualSchwartz, smul_apply, schwartzPhysicalDilation_apply,
    normalizedCutoffResidualSchwartz_apply χ hχ hχone hχzero a L m hL Q hQ]
  rw [hs, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hL]
  congr 2
  ring_nf

theorem exists_cutoffResidual_sampling_bound (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q), ∀ D : ℝ, 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L),
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel
          (cutoffResidualSchwartz χ hχ hχone hχzero a L (lt_of_lt_of_le zero_lt_one hL) m Q hQ))‖ ≤
            C * L ^ (-2 - a) := by
  obtain ⟨N, J, hJ, hsampling⟩ := exists_schwartzTorusSample_physicalJet_bound a k ha1 hk
  refine ⟨N + 1, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨B, hB, hjets⟩ := exists_normalizedCutoffResidual_uniform_jets χ hχ hχone hχzero
    a ha m N D hD Q hQ hsymbol
  refine ⟨J * B, mul_nonneg hJ hB, ?_⟩
  intro L hL
  let ψ := normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L m Q hQ
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hbase : ‖schwartzTorusSample a k 1 ha1 hk (by norm_num) (radianFourierKernel ψ)‖ ≤ J * B :=
    hsampling ψ B hB (hjets L hL) 1 (by norm_num)
  have hd := schwartzTorusSample_homogeneousDilation_norm_le a k L L ha ha1 hk hL le_rfl
    (radianFourierKernel ψ)
  simp only [div_self hLp.ne'] at hd
  have hscale : ‖schwartzTorusSample a k L ha1 hk hL
      (radianFourierKernel (schwartzPhysicalDilation a L hLp ψ))‖ ≤ L ^ (-a) * (J * B) := by
    rw [radianFourierKernel_schwartzPhysicalDilation]
    exact hd.trans (mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hLp.le _))
  change ‖physicalSchwartzTorusSamplingLinear a k L ha1 hk hL
    (((L ^ (-2 : ℝ) : ℝ) : ℂ) • schwartzPhysicalDilation a L hLp ψ)‖ ≤ _
  rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hLp.le _)]
  calc
    _ ≤ L ^ (-2 : ℝ) * (L ^ (-a) * (J * B)) :=
      mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hLp.le _)
    _ = (J * B) * L ^ (-2 - a) := by
      rw [← mul_assoc, ← Real.rpow_add hLp]
      ring_nf

/-- The sampled object in the norm estimate represents exactly the three
displayed terms of the physical PDE residual. -/
theorem exists_actualCutoffResidual_bound (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (_hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L), ∃ R : 𝓢(E, ℂ),
        (∀ y : E, R y = cutoffResidual m L χ Q y) ∧
        ‖schwartzTorusSample a k L ha1 hk hL (radianFourierKernel R)‖ ≤
          C * L ^ (-2 - a) := by
  obtain ⟨N, hN⟩ := exists_cutoffResidual_sampling_bound a k ha ha1 hk m χ hχ hχone hχzero
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨C, hC, hbound⟩ := hN Q hQ D hD hsymbol
  refine ⟨C, hC, ?_⟩
  intro L hL
  refine ⟨cutoffResidualSchwartz χ hχ hχone hχzero a L (lt_of_lt_of_le zero_lt_one hL) m Q hQ, ?_, hbound L hL⟩
  exact cutoffResidualSchwartz_apply χ hχ hχone hχzero a L (lt_of_lt_of_le zero_lt_one hL) m ham Q hQ

end DefocusingNLS

end OAI
