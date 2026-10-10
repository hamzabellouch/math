import OAI.Geometry.RCD.Sobolev.ScaledStampacchia
import OAI.Geometry.RCD.Sobolev.PoissonHeight

namespace OAI

/-! # Torsion bounds with the correct radius-squared scaling -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A normalized Sobolev inequality gives a torsion height proportional to
its length-squared parameter, uniformly as the volume tends to zero. -/
theorem exists_normalized_torsion_bound {d C : ℝ} (hd : 1 < d) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set X), μ Ω ≠ ∞ → 0 < μ.real Ω →
      ∀ s : ℝ, 0 < s → ∀ u : SobolevSpace.dirichlet μ hQ Ω,
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        energyForm μ hQ u.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) →
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
          (C * s * (μ.real Ω) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val) →
      ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ hQ u.val x ≤ K * s := by
  obtain ⟨K, hK, hExt⟩ := exists_scaled_extinction_level
    (Real.rpow_nonneg hC (2 * d)) (by linarith : 2 < 2 * d)
  refine ⟨K, hK, ?_⟩
  intro Ω hfin hvol s hs u hsolve hsob
  let ν := μ.restrict Ω
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let U := fun x => SobolevSpace.toLp μ hQ u.val x
  let Y := fun t : ℝ => ν.real {x | t < U x}
  let V := μ.real Ω
  let Cs := C * s * V ^ (1 / d - 1)
  have hCs : 0 ≤ Cs := mul_nonneg (mul_nonneg hC hs.le) (Real.rpow_nonneg hvol.le _)
  have hY0 : Y 0 ≤ V := by
    have hh := measureReal_mono (μ := ν) (subset_univ {x | 0 < U x}) (measure_ne_top ν univ)
    simpa only [ν, measureReal_restrict_apply_univ, V, Y] using hh
  have hmono (k l : ℝ) (_hk : 0 ≤ k) (hkl : k ≤ l) : Y l ≤ Y k := by
    apply measureReal_mono _ (measure_ne_top ν _)
    intro x hx
    exact hkl.trans_lt hx
  have hstep (k l : ℝ) (hk : 0 ≤ k) (hkl : k < l) :
      Y l ≤ Cs ^ (2 * d) * Y k ^ (2 * d - 1) / (l - k) ^ (2 * d) := by
    have hm : Y l ≤ ν.real {x | l ≤ U x} := by
      apply measureReal_mono _ (measure_ne_top ν _)
      intro x hx
      exact (show l < U x from hx).le
    exact hm.trans (torsion_superlevel_le μ hQ Ω hfin u hsolve hd hCs hsob hk hkl)
  have hz : Y (K * s) = 0 := hExt (Cs ^ (2 * d)) V s hvol hs
    (normalized_sobolev_coefficient hC hs hvol hd) Y
    (fun _ _ => measureReal_nonneg) hY0 hmono hstep
  have hz' : ν {x | K * s < U x} = 0 :=
    (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top ν _)
  apply ae_iff.mpr
  simpa only [not_le] using hz'

/-- Coercivity constructs the torsion solution; normalized Sobolev controls
its height by a uniform multiple of the length-squared parameter. -/
theorem exists_uniform_normalized_bounded_torsion {d C : ℝ} (hd : 1 < d) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set X), MeasurableSet Ω → μ Ω ≠ ∞ → 0 < μ.real Ω →
      ∀ s : ℝ, 0 < s → ∀ P : ℝ, 0 ≤ P →
      (∀ v : SobolevSpace.dirichlet μ hQ Ω,
        ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val) →
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
          (C * s * (μ.real Ω) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val) →
      ∃ τ : SobolevSpace.dirichlet μ hQ Ω,
        (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
          energyForm μ hQ τ.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) ∧
        (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ τ.val x ∧
          SobolevSpace.toLp μ hQ τ.val x ≤ K * s) := by
  obtain ⟨K, hK, hb⟩ := exists_normalized_torsion_bound μ hQ hd hC
  refine ⟨K, hK, ?_⟩
  intro Ω hΩ hfin hvol s hs P hP hpoin hsob
  let F := dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin 1)
  have hF (φ : SobolevSpace.dirichlet μ hQ Ω) :
      F φ = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ := by
    simpa only [F, one_mul] using dirichletSource_indicator μ hQ Ω hΩ hfin 1 φ
  have hpos (φ : SobolevSpace.dirichlet μ hQ Ω)
      (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) : 0 ≤ F φ := by
    rw [hF]
    exact integral_nonneg_of_ae (ae_restrict_of_ae hφ)
  obtain ⟨τ, hτ, hτ0⟩ := exists_nonnegative_dirichlet_solution μ hQ Ω hP hpoin F hpos
  have hsolve (φ : SobolevSpace.dirichlet μ hQ Ω) := (hτ φ).trans (hF φ)
  have hτK := hb Ω hfin hvol s hs τ hsolve hsob
  have hupper : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ τ.val x ≤ K * s := by
    apply ae_of_ae_restrict_of_ae_restrict_compl Ω hτK
    filter_upwards [SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ τ] with x hx
    rw [hx]
    exact mul_nonneg hK.le hs.le
  exact ⟨τ, hsolve, hτ0.and hupper⟩

end RegularPointCoordinates

end

end OAI
