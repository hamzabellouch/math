import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalizedWeakLimit

namespace OAI

/-! # Local uniform convergence of the actual expanding-torus functions

Once the radii diverge, a cutoff that equals one near the origin disappears
from every fixed physical ball.  The weak localization limit then gives
uniform convergence of the original torus functions on that ball.
-/

open Filter Topology Set
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem eventually_expandingCutoff_one (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (hLinf : Tendsto L atTop atTop) (χ : 𝓢(E, ℂ)) (ρ R : ℝ) (hρ : 0 < ρ)
    (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1) :
    ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R → χ ((L n)⁻¹ • y) = 1 := by
  filter_upwards [hLinf.eventually (eventually_ge_atTop (R / ρ))] with n hn y hy
  apply hχ
  have hLp : 0 < L n := by linarith [hL n]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hLp)]
  calc
    (L n)⁻¹ * ‖y‖ ≤ (L n)⁻¹ * R := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hLp.le)
    _ = R / L n := by ring
    _ ≤ ρ := (div_le_iff₀ hLp).mpr (by
      have hb := (div_le_iff₀ hρ).mp hn
      nlinarith)

theorem expandingTorus_local_uniform_of_localized_weak (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (f : ℕ → FourierL2) (v : HomogeneousY a k)
    (hbound : ∀ n, ‖homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)))
        atTop (𝓝 (ℓ v))) :
    ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y)) -
        homogeneousPhysicalCLM a k ha ha1 hk v y‖ < ε := by
  intro R ε hε
  let S := Metric.closedBall (0 : E) R
  let u := fun n => homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)
  let J := homogeneousLocalObservation a k ha ha1 hk S
  have hJ := homogeneousLocalObservation_of_weakLimit a k M ha ha1 hk S u v hbound hweak
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp hJ
  have hsmall : ∀ᶠ n in atTop, ‖J (u n) - J v‖ < ε :=
    hnorm.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall, eventually_expandingCutoff_one L hL hLinf χ ρ R hρ hχ]
    with n hn hcut y hy
  have hyS : y ∈ S := by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hy
  have hb := (J (u n) - J v).norm_coe_le_norm ⟨y, hyS⟩
  have hp : J (u n) ⟨y, hyS⟩ =
      expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y)) := by
    rw [homogeneousLocalObservation_apply, homogeneousLocalization_physical]
    exact (congrArg (fun z : ℂ => z *
      expandingTorusFunction a k (L n) (f n) (euclideanToTorus ((L n)⁻¹ • y))) (hcut y hy)).trans
        (one_mul _)
  change ‖J (u n) ⟨y, hyS⟩ - J v ⟨y, hyS⟩‖ ≤ ‖J (u n) - J v‖ at hb
  rw [hp] at hb
  exact hb.trans_lt hn

theorem exists_expandingTorus_local_limit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) :
    ∃ v : HomogeneousY a k, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L (φ n))
          ha ha1 hk (hL (φ n)) χ (f (φ n)))) atTop (𝓝 (ℓ v))) ∧
      (∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
        ‖expandingTorusFunction a k (L (φ n)) (f (φ n))
            (euclideanToTorus ((L (φ n))⁻¹ • y)) -
          homogeneousPhysicalCLM a k ha ha1 hk v y‖ < ε) := by
  obtain ⟨_, _, v, _, φ, hφ, hweak, _⟩ :=
    exists_expandingLocalized_weakLimit a k M ha ha1 hk L hL χ f hf
  obtain ⟨C, hC, hb⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  refine ⟨v, φ, hφ, hweak, ?_⟩
  exact expandingTorus_local_uniform_of_localized_weak a k (C * M) ha ha1 hk
    (L ∘ φ) (fun n => hL (φ n)) (hLinf.comp hφ.tendsto_atTop) χ ρ hρ hχ
    (f ∘ φ) v (fun n => (hb _ (hL (φ n)) _).trans
      (mul_le_mul_of_nonneg_left (hf (φ n)) hC)) hweak

end DefocusingNLS

end OAI
