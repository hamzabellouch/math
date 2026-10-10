import OAI.Geometry.RCD.Harmonic.HarmonicQuadraticPotential

namespace OAI

/-! # Compact cutoff tests for the harmonic quadratic model -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] in
private theorem bounded_product_bound (f g : SobolevSpace μ hQ) (C D : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x| ≤ D) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ f g C D) x| ≤
      (C * D : ℝ≥0) := by
  filter_upwards [SobolevSpace.product_coe μ hQ f g C D hf hg, hf, hg] with x hx hfx hgx
  rw [hx, abs_mul]
  exact mul_le_mul hfx hgx (abs_nonneg _) C.coe_nonneg

variable [ProperSpace X]

/-- Testing the quadratic model against an actual cutoff times a bounded
Sobolev function is legitimate in every harmonic coordinate equation. -/
theorem coordinateQuadratic_cutoff_energy {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C D E L : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c w : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ E) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ D) :
    energyForm μ hQ (coordinateQuadratic μ hQ u C) (SobolevSpace.product μ hQ c w E D) =
      -(∫ x, SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ c w E D) x *
        (∑ j, localGamma μ hQ (u j) (u j) x) ∂μ) := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ E := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  let φ := SobolevSpace.product μ hQ c w E D
  have hφ := bounded_product_bound μ hQ c w E D hc hw
  apply coordinateQuadratic_energy μ hQ u C (E * D) φ hu hub hφ
  intro j
  let t := SobolevSpace.product μ hQ (u j) w C D
  let tχ := SobolevSpace.cutoffCLM μ hQ hχ hcpt hbound hnonneg t
  have heq : SobolevSpace.product μ hQ (u j) φ C (E * D) = tχ := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.product_coe μ hQ (u j) φ C (E * D) (hub j) hφ,
      SobolevSpace.product_coe μ hQ c w E D hc hw, hcrep,
      SobolevSpace.product_coe μ hQ (u j) w C D (hub j) hw,
      SobolevSpace.cutoffCLM_coe μ hQ hχ hcpt hbound hnonneg t] with x hp hφx hcx htx hcut
    change SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ (u j) φ C (E * D)) x =
      SobolevSpace.toLp μ hQ tχ x
    rw [hp, hφx, hcx, hcut, htx]
    ring
  rw [heq]
  exact SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hcpt hbound hnonneg hsupp t

/-- The exact cross-term identity used in qualitative convergence of the
distance gradient. The quadratic model's source is the actual Gram trace. -/
theorem coordinateQuadratic_cutoff_cross {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C D E L : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c w : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ E) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ D) :
    (∫ x, SobolevSpace.toLp μ hQ c x *
      localGamma μ hQ w (coordinateQuadratic μ hQ u C) x ∂μ) =
      -(∫ x, SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ c w E D) x *
        (∑ j, localGamma μ hQ (u j) (u j) x) ∂μ) -
      ∫ x, SobolevSpace.toLp μ hQ w x * localGamma μ hQ c (coordinateQuadratic μ hQ u C) x ∂μ := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ E := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have he := coordinateQuadratic_cutoff_energy μ hQ u C D E L hu hub c w χ
    hχ hcpt hbound hnonneg hsupp hcrep hw
  rw [energyForm_comm] at he
  rw [energy_bounded_product μ hQ c w (coordinateQuadratic μ hQ u C) E D hc hw] at he
  linarith

end RegularPointCoordinates

end

end OAI
