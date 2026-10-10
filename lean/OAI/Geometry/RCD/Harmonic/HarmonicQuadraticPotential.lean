import OAI.Geometry.RCD.Sobolev.MeasureProductEnergy
import OAI.Geometry.RCD.Harmonic.LocalCaccioppoli
import OAI.Geometry.RCD.Sobolev.DirichletPoisson

namespace OAI

/-! # The local equation for the square of a harmonic coordinate -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
/-- A bounded Sobolev function multiplied by an actual compact Lipschitz
cutoff belongs to the canonical zero-boundary space. -/
theorem bounded_cutoff_product_mem_dirichlet (Ω : Set X)
    (c u : SobolevSpace μ hQ) (C D L : ℝ≥0)
    (χ : X → ℝ) (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ C) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hu : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ D) :
    SobolevSpace.product μ hQ c u C D ∈ SobolevSpace.dirichlet μ hQ Ω := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ C := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have he : SobolevSpace.product μ hQ c u C D =
      SobolevSpace.cutoffCLM μ hQ hχ hcpt hbound hnonneg u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.product_coe μ hQ c u C D hc hu, hcrep,
      SobolevSpace.cutoffCLM_coe μ hQ hχ hcpt hbound hnonneg u] with x hp hx ht
    exact hp.trans ((congrArg (· * SobolevSpace.toLp μ hQ u x) hx).trans ht.symm)
  rw [he]
  exact SobolevSpace.cutoffCLM_mem_dirichlet μ hQ hχ hcpt hbound hnonneg hsupp u

/-- The local distributional Laplacian of half the square of a harmonic
coordinate is its actual energy density. No second-order input is used. -/
theorem harmonic_half_square_energy {Ω : Set X} (u φ : SobolevSpace μ hQ)
    (C D : ℝ≥0) (hu : IsSobolevHarmonicOn μ hQ Ω u)
    (hub : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ C)
    (hφb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ φ x| ≤ D)
    (hprod : SobolevSpace.product μ hQ u φ C D ∈ SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ u C) φ =
      -(∫ x, SobolevSpace.toLp μ hQ φ x * localGamma μ hQ u u x ∂μ) := by
  have he := energy_product_integration_by_parts μ hQ u u φ C C D hub hub hφb
  rw [hu _ hprod] at he
  have hsq : SobolevSpace.product μ hQ u u C C = SobolevSpace.square μ hQ u C := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [SobolevSpace.product_coe μ hQ u u C C hub hub,
      SobolevSpace.square_coe μ hQ u C hub] with x hp hs
    change SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u u C C) x =
      SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ u C) x
    rw [hp, hs, pow_two]
  rw [hsq] at he
  rw [energyForm_smul_left, he]
  ring

/-- The actual Euclidean quadratic model associated to bounded harmonic
coordinates. Its gradient is used to compare distance gradients. -/
def coordinateQuadratic {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0) :
    SobolevSpace μ hQ := ∑ j, (1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C

theorem coordinateQuadratic_energy {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C D : ℝ≥0) (φ : SobolevSpace μ hQ)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (hφb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ φ x| ≤ D)
    (hprod : ∀ j, SobolevSpace.product μ hQ (u j) φ C D ∈ SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ (coordinateQuadratic μ hQ u C) φ =
      -(∫ x, SobolevSpace.toLp μ hQ φ x * (∑ j, localGamma μ hQ (u j) (u j) x) ∂μ) := by
  have hi (j : Fin n) : Integrable (fun x =>
      SobolevSpace.toLp μ hQ φ x * localGamma μ hQ (u j) (u j) x) μ :=
    (localGamma_memL1 μ hQ (u j) (u j)).bdd_mul
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ φ))
      (by simpa only [Real.norm_eq_abs] using hφb)
  calc
    _ = ∑ j, energyForm μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C) φ := by
      rw [energyForm_comm]
      change (sobolevEnergyForm μ hQ φ) (∑ j, _) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => energyForm_comm μ hQ _ _
    _ = ∑ j, -(∫ x, SobolevSpace.toLp μ hQ φ x * localGamma μ hQ (u j) (u j) x ∂μ) :=
      Finset.sum_congr rfl fun j _ => harmonic_half_square_energy μ hQ (u j) φ C D
        (hu j) (hub j) hφb (hprod j)
    _ = -(∫ x, ∑ j, SobolevSpace.toLp μ hQ φ x * localGamma μ hQ (u j) (u j) x ∂μ) := by
      rw [Finset.sum_neg_distrib, integral_finsetSum _ (fun j _ => hi j)]
    _ = _ := by simp only [Finset.mul_sum]

omit [BorelSpace X] [ProperSpace X] in
theorem coordinateQuadratic_representative {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (C : ℝ≥0)
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C) :
    SobolevSpace.toLp μ hQ (coordinateQuadratic μ hQ u C) =ᵐ[μ]
      fun x => ∑ j, (1 / 2 : ℝ) * (SobolevSpace.toLp μ hQ (u j) x) ^ 2 := by
  have hj (j : Fin n) : SobolevSpace.toLp μ hQ
      ((1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C) =ᵐ[μ]
        fun x => (1 / 2 : ℝ) * (SobolevSpace.toLp μ hQ (u j) x) ^ 2 := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ)
      (SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (u j) C)),
      SobolevSpace.square_coe μ hQ (u j) C (hub j)] with x hsm hs
    change (((1 / 2 : ℝ) • SobolevSpace.toLp μ hQ (SobolevSpace.square μ hQ (u j) C)) x) = _
    simp only [hsm, Pi.smul_apply, smul_eq_mul, hs]
  have hall := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun j _ => hj j)
  have hsum := Lp.coeFn_finsetSum (Finset.univ : Finset (Fin n))
    (fun j => SobolevSpace.toLp μ hQ ((1 / 2 : ℝ) • SobolevSpace.square μ hQ (u j) C))
  unfold coordinateQuadratic
  rw [map_sum]
  filter_upwards [hsum, hall] with x hx hjx
  rw [hx]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j hj => hjx j hj

end RegularPointCoordinates

end

end OAI
