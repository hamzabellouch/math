import OAI.Geometry.RCD.Coordinates.RebasedRadialFits
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction
import OAI.Geometry.RCD.Harmonic.CenteredAffineDifference

namespace OAI

/-! # Transporting the actual radial fits to a common frame and region -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- The common-frame residual is exactly the original residual at the
transported covector, including its recentering constant. -/
theorem common_frame_radial_residual {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ)
    (G : Euclidean n →L[ℝ] SobolevSpace μ hQ) (x z : Euclidean n)
    (N M : Euclidean n ≃L[ℝ] Euclidean n) (C : Euclidean n →L[ℝ] Euclidean n)
    (b : Euclidean n) :
    G (M.symm (N b)) -
      (centeredSobolevMap μ hQ u η z).comp N.toContinuousLinearMap
        (rebasedRadialOperator N M C b) -
      ⟪z - x, C (M.symm (N b))⟫_ℝ • η =
    G (M.symm (N b)) - centeredAffineSobolev μ hQ u η x (C (M.symm (N b))) := by
  rw [centered_radial_rebase μ hQ u η x z N M C b]
  module

omit [ProperSpace X] in
/-- The volume ratio and frame operator norm account for all losses when
the original all-covector radial fit is used on the common commutator region. -/
theorem common_frame_radial_bounds {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ)
    (G : Euclidean n →L[ℝ] SobolevSpace μ hQ) (x z : Euclidean n)
    (N M : Euclidean n ≃L[ℝ] Euclidean n) (C : Euclidean n →L[ℝ] Euclidean n)
    {Ωv Ωe Ω : Set X} (hΩv : Ω ⊆ Ωv) (hΩe : Ω ⊆ Ωe)
    (hvfin : μ Ωv ≠ ∞) (hfin : μ Ω ≠ ∞)
    (hvpos : 0 < μ.real Ωv) (hepos : 0 < μ.real Ωe) (hpos : 0 < μ.real Ω)
    {V W E D : ℝ} (hE : 0 ≤ E) (hD : 0 ≤ D)
    (hvolv : μ.real Ωv ≤ V * μ.real Ω) (hvole : μ.real Ωe ≤ W * μ.real Ω)
    (hvalue : ∀ a, ‖normalizeLocalL2 μ Ωv hvfin (SobolevSpace.restrictLp μ hQ Ωv
      (G a - centeredAffineSobolev μ hQ u η x (C a)))‖ ^ 2 ≤ E * ‖a‖ ^ 2)
    (henergy : ∀ a, (μ.real Ωe)⁻¹ * (∫ t in Ωe, localGamma μ hQ
      (G a - centeredAffineSobolev μ hQ u η x (C a))
      (G a - centeredAffineSobolev μ hQ u η x (C a)) t ∂μ) ≤ D * ‖a‖ ^ 2)
    (b : Euclidean n) :
    let P := M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap
    let R := G (P b) -
      (centeredSobolevMap μ hQ u η z).comp N.toContinuousLinearMap
        (rebasedRadialOperator N M C b) - ⟪z - x, C (P b)⟫_ℝ • η
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω R)‖ ^ 2 ≤
      V * (E * ‖P‖ ^ 2) * ‖b‖ ^ 2 ∧
    (μ.real Ω)⁻¹ * (∫ t in Ω, localGamma μ hQ R R t ∂μ) ≤
      W * (D * ‖P‖ ^ 2) * ‖b‖ ^ 2 := by
  dsimp only
  have hrebase := common_frame_radial_residual μ hQ u η G x z N M C b
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hrebase ⊢
  rw [hrebase]
  let P := M.symm.toContinuousLinearMap.comp N.toContinuousLinearMap
  have hnorm (F : ℝ) (hF : 0 ≤ F) : F * ‖P b‖ ^ 2 ≤ F * ‖P‖ ^ 2 * ‖b‖ ^ 2 := by
    calc
      _ ≤ F * (‖P‖ * ‖b‖) ^ 2 := by gcongr; exact P.le_opNorm b
      _ = _ := by ring
  have hv := normalized_fit_restrict_sq μ hQ hΩv hvfin hfin hvpos hpos
    (G (P b) - centeredAffineSobolev μ hQ u η x (C (P b)))
    (mul_nonneg (mul_nonneg hE (sq_nonneg _)) (sq_nonneg _)) hvolv
    ((hvalue (P b)).trans (hnorm E hE))
  have he := normalized_fit_energy_restrict μ hQ hΩe hepos hpos
    (G (P b) - centeredAffineSobolev μ hQ u η x (C (P b)))
    (mul_nonneg (mul_nonneg hD (sq_nonneg _)) (sq_nonneg _)) hvole
    ((henergy (P b)).trans (hnorm D hD))
  constructor
  · simpa only [P, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, mul_assoc] using hv
  · simpa only [P, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, mul_assoc] using he

omit [BorelSpace X] [ProperSpace X] in
/-- Centering the common harmonic column changes each covector by a
locally constant function, represented by the same compact cutoff. -/
theorem centered_sobolev_constant_difference {n : ℕ}
    (Ω : Set X) (u : Fin n → SobolevSpace μ hQ) (η : SobolevSpace μ hQ)
    (z b : Euclidean n)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) :
    SobolevSpace.toLp μ hQ (centeredSobolevMap μ hQ u η z b - sobolevColumnMap μ hQ u b)
      =ᵐ[μ.restrict Ω] fun _ => -⟪z, b⟫_ℝ := by
  have he : centeredSobolevMap μ hQ u η z b - sobolevColumnMap μ hQ u b =
      (-⟪z, b⟫_ℝ) • η := by
    simp only [centeredSobolevMap, sub_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    module
  rw [he]
  change SobolevSpace.toLpCLM μ hQ ((-⟪z, b⟫_ℝ) • η) =ᵐ[μ.restrict Ω] _
  rw [map_smul]
  filter_upwards [hη, ae_restrict_of_ae
    (Lp.coeFn_smul (-⟪z, b⟫_ℝ) (SobolevSpace.toLp μ hQ η))] with x hx hs
  change ((-⟪z, b⟫_ℝ) • SobolevSpace.toLp μ hQ η) x = _
  simp only [hs, Pi.smul_apply, smul_eq_mul, hx, mul_one]

/-- The transported radial family remains a representative of the
derivative of the same centered coordinate map in the common frame. -/
theorem common_frame_radial_representative {n : ℕ}
    (Ω : Set X) (f : SobolevSpace μ hQ) (u : Fin n → SobolevSpace μ hQ)
    (η : SobolevSpace μ hQ) (z : Euclidean n)
    (N M : Euclidean n ≃L[ℝ] Euclidean n)
    (G : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hG : ∀ a, SobolevSpace.toLp μ hQ (G a) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f (sobolevColumnMap μ hQ u (M a))) (b : Euclidean n) :
    SobolevSpace.toLp μ hQ (G (M.symm (N b))) =ᵐ[μ.restrict Ω]
      localGamma μ hQ f ((centeredSobolevMap μ hQ u η z).comp N.toContinuousLinearMap b) := by
  have hrep := hG (M.symm (N b))
  rw [M.apply_symm_apply] at hrep
  have hd := localGamma_eq_of_constant_difference μ hQ Ω
    (centeredSobolevMap μ hQ u η z (N b)) (sobolevColumnMap μ hQ u (N b)) f
    (-⟪z, N b⟫_ℝ) (centered_sobolev_constant_difference μ hQ Ω u η z (N b) hη)
  filter_upwards [hrep, hd,
    ae_restrict_of_ae (localGamma_comm μ hQ f (centeredSobolevMap μ hQ u η z (N b))),
    ae_restrict_of_ae (localGamma_comm μ hQ f (sobolevColumnMap μ hQ u (N b)))]
    with x hr hd hc hc'
  change _ = localGamma μ hQ f (centeredSobolevMap μ hQ u η z (N b)) x
  exact hr.trans (hc'.trans (hd.symm.trans hc.symm))

end RegularPointCoordinates

end

end OAI
