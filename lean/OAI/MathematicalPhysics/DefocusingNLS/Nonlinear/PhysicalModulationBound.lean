import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationTaylor

namespace OAI

/-! # A uniform first-order bound for the actual modulation chart -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

theorem modulatedCutoffProfile_bound (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : Radius, 2 ≤ L.1 → ∀ p : Params,
      ‖p‖ ≤ 1 / 2 → ‖p‖ ≤ 2 * Real.log 2 →
      ‖modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ L p‖ ≤ C * ‖p‖ := by
  obtain ⟨A, hA, hfirst⟩ := cutoffProfile_mixed_first_bound a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  obtain ⟨B, hB, hsample⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨6 * A + 4 * B, by positivity, ?_⟩
  intro L hL p hp hplog
  have hθ : |p.1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le p
  have hv : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
  have ht : |p.2.2| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le p.2).trans (norm_snd_le p)
  let z : ℂ := (a * p.2.2 : ℝ) - (p.1 : ℂ) * Complex.I
  let u := sobolevTranslation (euclideanToTorus ((1 / L.1) • p.2.1))
    (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 p.2.2))
  let q := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1
  have hz : ‖z‖ ≤ 2 * ‖p‖ := by
    have h := norm_sub_le ((a * p.2.2 : ℝ) : ℂ) ((p.1 : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos ha] at h
    change ‖z‖ ≤ a * |p.2.2| + |p.1| at h
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (abs_nonneg p.2.2)]
  have hexp : ‖Complex.exp z - 1‖ ≤ 4 * ‖p‖ :=
    (complex_exp_sub_one_bound z (by linarith)).trans (by linarith)
  have hnexp : ‖Complex.exp z‖ ≤ 3 := by
    have h := norm_le_norm_sub_add (Complex.exp z) 1
    simp only [norm_one] at h
    linarith
  have hu : ‖u - q‖ ≤ 2 * A * ‖p‖ := by
    apply (hfirst L hL p.2.2 p.2.1 (ht.trans hplog) (by linarith)).trans
    nlinarith
  have hq : ‖q‖ ≤ B := by
    simpa only [q, fixedCutoffProfile_self, physicalSchwartzTorusSamplingCLM_apply] using hsample L.1 L.2
  have he : Complex.exp z • u - q =
      Complex.exp z • (u - q) + (Complex.exp z - 1) • q := by
    rw [smul_sub, sub_smul, one_smul]
    abel
  change ‖Complex.exp z • u - q‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖Complex.exp z • (u - q)‖ + ‖(Complex.exp z - 1) • q‖ := norm_add_le _ _
    _ = ‖Complex.exp z‖ * ‖u - q‖ + ‖Complex.exp z - 1‖ * ‖q‖ := by rw [norm_smul, norm_smul]
    _ ≤ 3 * (2 * A * ‖p‖) + (4 * ‖p‖) * B := add_le_add
      (mul_le_mul hnexp hu (norm_nonneg _) (by norm_num))
      (mul_le_mul hexp hq (norm_nonneg _) (by positivity))
    _ = _ := by ring

end DefocusingNLS

end OAI
