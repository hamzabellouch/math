import OAI.Geometry.RCD.Sobolev.QuadraticValueGradientBound
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # Uniform constants in the quadratic-model gradient comparison -/

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Cauchy--Schwarz with the actual local square-gradient bounds. -/
theorem gamma_abs_le_of_bounds {Ω : Set X} (f g : SobolevSpace μ hQ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ A ^ 2)
    (hg : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ g g x ≤ B ^ 2) :
    ∀ᵐ x ∂μ.restrict Ω, |localGamma μ hQ f g x| ≤ A * B := by
  filter_upwards [hf, hg, ae_restrict_of_ae (localGamma_sq_le μ hQ f g),
    ae_restrict_of_ae (localGamma_self μ hQ g)] with x hfx hgx hcs hself
  have hs := hcs.trans (mul_le_mul hfx hgx (by rw [hself]; positivity) (sq_nonneg A))
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA hB)).mp
  simpa only [sq_abs, mul_pow] using hs

/-- Bounded coordinate values and gradients control the cutoff cross term
of their actual quadratic potential. -/
theorem coordinateQuadratic_cutoff_bound {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) (c : SobolevSpace μ hQ)
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hu : ∀ j, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (u j) (u j) x ≤ M ^ 2)
    (hc : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ c c x ≤ L ^ 2) :
    ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ hQ c (coordinateQuadratic μ hQ u C) x| ≤ (n : ℝ) * C * M * L := by
  have hp := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun j _ => gamma_abs_le_of_bounds μ hQ (u j) c hM hL (hu j) hc)
  have hb := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr (fun j _ => hub j)
  filter_upwards [hp, ae_restrict_of_ae hb,
    ae_restrict_of_ae (localGamma_comm μ hQ c (coordinateQuadratic μ hQ u C)),
    ae_restrict_of_ae (coordinateQuadratic_gradient μ hQ u C c hub)] with x hx hb hc hg
  rw [hc, hg]
  calc
    _ ≤ ∑ j, |SobolevSpace.toLp μ hQ (u j) x * localGamma μ hQ (u j) c x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (C : ℝ) * (M * L) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul (hb j hj) (hx j hj) (abs_nonneg _) C.coe_nonneg
    _ = _ := by simp; ring

/-- The gradient comparison now has explicit constants from coordinate
and cutoff bounds, with no separate cross-term assumption. -/
theorem coordinateQuadratic_uniform_value_gradient {n : ℕ} {Ω : Set X}
    (hfin : μ Ω ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (C D Lχ : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c q : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith Lχ χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ 1) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D)
    {δ M L : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hsmall : ∀ᵐ x ∂μ.restrict Ω,
      |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ δ)
    (heik : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x)
    (hgrad : ∀ j, ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ (u j) (u j) x ≤ M ^ 2)
    (hcut : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ c c x ≤ L ^ 2) :
    let H := coordinateQuadratic μ hQ u C
    (∫ x in Ω, SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) (q - H) x ∂μ) ≤
      2 * δ * (1 + (n : ℝ) * M ^ 2 + (n : ℝ) * C * M * L) * μ.real Ω +
        (C : ℝ) ^ 2 * ∫ x in Ω, ∑ i, ∑ j,
          |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0| ∂μ := by
  have ht : ∀ᵐ x ∂μ.restrict Ω, (∑ j, localGamma μ hQ (u j) (u j) x) ≤ (n : ℝ) * M ^ 2 := by
    filter_upwards [(Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
      (fun j _ => hgrad j)] with x hx
    calc
      _ ≤ ∑ _j : Fin n, M ^ 2 := Finset.sum_le_sum hx
      _ = _ := by simp
  exact coordinateQuadratic_value_gradient_bound μ hQ hfin u C D Lχ hu hub c q χ
    hχ hcpt hbound hnonneg hsupp hcrep hw hδ hsmall heik ht
    (coordinateQuadratic_cutoff_bound μ hQ u C c hub hM hL hgrad hcut)

end RegularPointCoordinates

end

end OAI
