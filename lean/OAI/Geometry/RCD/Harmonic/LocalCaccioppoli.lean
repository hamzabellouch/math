import OAI.Geometry.RCD.Harmonic.HarmonicGrams

namespace OAI

/-! # Local harmonic cutoff tests in the canonical Dirichlet space -/

open Set MeasureTheory
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A compactly supported Lipschitz cutoff supplies an admissible squared
cutoff test against any bounded Sobolev function. -/
theorem square_cutoff_product_mem_dirichlet
    (Ω : Set X) (u η : SobolevSpace μ hQ) (C D L : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (v : X → ℝ) (hv : LipschitzWith L v) (hs : HasCompactSupport v)
    (hb : ∀ x, |v x| ≤ D) (hΩ : tsupport v ⊆ Ω)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v) :
    SobolevSpace.product μ hQ (SobolevSpace.square μ hQ η D) u (D * D) C ∈
      SobolevSpace.dirichlet μ hQ Ω := by
  have hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D := by
    filter_upwards [hrep] with x hx
    simpa only [hx] using hb x
  obtain ⟨L₂, hL₂⟩ := lipschitz_mul_constant_outside_compact hv hv 0
    (by simpa using hs) hb
  have hs₂ : HasCompactSupport (fun x => v x * v x) := hs.mul_right
  have hb₂ (x : X) : |v x * v x| ≤ (D * D : ℝ≥0) := by
    rw [abs_mul]
    exact mul_le_mul (hb x) (hb x) (abs_nonneg _) D.coe_nonneg
  have hn₂ (x : X) : 0 ≤ v x * v x := mul_self_nonneg _
  have hΩ₂ : tsupport (fun x => v x * v x) ⊆ Ω :=
    (tsupport_mul_subset_left : tsupport (fun x => v x * v x) ⊆ tsupport v).trans hΩ
  let test := SobolevSpace.product μ hQ (SobolevSpace.square μ hQ η D) u (D * D) C
  let cutoff := SobolevSpace.cutoffCLM μ hQ hL₂ hs₂ hb₂ hn₂ u
  have hsq : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ η D) x| ≤
      (D * D : ℝ≥0) := by
    filter_upwards [SobolevSpace.square_coe μ hQ η D hη, hη] with x hx hb
    rw [hx, abs_pow, sq_abs]
    have hh := (sq_le_sq₀ (abs_nonneg _) D.coe_nonneg).mpr hb
    rw [sq_abs] at hh
    simpa only [NNReal.coe_mul, pow_two] using hh
  have heq : test = cutoff := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.product_coe μ hQ (SobolevSpace.square μ hQ η D) u
      (D * D) C hsq hu, SobolevSpace.square_coe μ hQ η D hη, hrep,
      SobolevSpace.cutoffCLM_coe μ hQ hL₂ hs₂ hb₂ hn₂ u] with x ht hsq hx hc
    change SobolevSpace.toLp μ hQ test x = SobolevSpace.toLp μ hQ cutoff x
    rw [ht, hsq, hx, hc]
    ring
  change test ∈ SobolevSpace.dirichlet μ hQ Ω
  rw [heq]
  exact SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hL₂ hs₂ hb₂ hn₂ hΩ₂ u

/-- Local harmonicity, rather than a global weak Laplacian, suffices for
the weighted Caccioppoli inequality when the cutoff is supported inside
the harmonicity domain. -/
theorem IsSobolevHarmonicOn.caccioppoli
    (Ω : Set X) (u η : SobolevSpace μ hQ) (C D L : ℝ≥0)
    (hharm : IsSobolevHarmonicOn μ hQ Ω u)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (v : X → ℝ) (hv : LipschitzWith L v) (hs : HasCompactSupport v)
    (hb : ∀ x, |v x| ≤ D) (hΩ : tsupport v ⊆ Ω)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v) :
    (∫ x, (SobolevSpace.toLp μ hQ η x) ^ 2 *
      (SobolevSpace.minimalSlope μ hQ u x) ^ 2 ∂μ) ≤
      4 * ∫ x, (SobolevSpace.toLp μ hQ u x) ^ 2 *
        (SobolevSpace.minimalSlope μ hQ η x) ^ 2 ∂μ := by
  have hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ D := by
    filter_upwards [hrep] with x hx
    simpa only [hx] using hb x
  exact caccioppoli_weighted μ hQ u η C D hu hη
    (hharm _ (square_cutoff_product_mem_dirichlet μ hQ Ω u η C D L hu v hv hs hb hΩ hrep))

end RegularPointCoordinates

end

end OAI
