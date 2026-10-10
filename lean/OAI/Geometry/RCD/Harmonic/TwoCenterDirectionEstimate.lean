import OAI.Geometry.RCD.Coordinates.TwoCenterCommutatorFit
import OAI.Geometry.RCD.Harmonic.TwoCenterAffineRecovery
import OAI.Geometry.RCD.Harmonic.ConstantDirectionError

namespace OAI

/-! # Absorbing the two-center commutator and recovering the direction -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The term involving the unknown matrix difference is absorbed using
the small radial value error. The resulting direction estimate uses the
same representatives as the two radial fits. -/
theorem two_center_direction_estimate {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X}
    (hgradient : LocalHarmonicL2GradientInput hX)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Cg Cm : ℝ, 1 ≤ Cg ∧ 1 ≤ Cm ∧
    ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
    ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (V : X → Euclidean n) (N : Euclidean n ≃L[ℝ] Euclidean n),
    IsExactMeanNormalization (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic u)
      (ball p (R / 2)) measurableSet_ball N →
    (∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) (u j)) →
    ContinuousOn V (ball p R) → V p = 0 →
    (∀ j, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u j) =ᵐ[
      (hausdorff n X).restrict (ball p R)] fun x => V x j) →
    ∀ (eta fz fx : SobolevSpace (hausdorff n X) hX.quadratic)
      (Gz Gx : Euclidean n →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (Az Ax : Euclidean n →L[ℝ] Euclidean n) (c d : Euclidean n →L[ℝ] ℝ)
      (Cf Cv Ez Ex Dz Dx Hcoord Mconst Com : ℝ),
    let μ := hausdorff n X
    let U := sobolevColumnMap μ hX.quadratic u
    let Ω := ball p R
    let hfin := ne_of_lt (hX.finiteOnBounded Ω isBounded_ball)
    let a := 2 * ‖N.toContinuousLinearMap‖ * (Cg / R)
    let e := Cv * Real.sqrt Dz + Real.sqrt Com + Cf * Real.sqrt (2 * Dz + 2 * Dx) +
      Real.sqrt (2 * Ez + 2 * Ex) * ‖Az - 1‖
    0 ≤ Cf → 0 ≤ Cv → 0 ≤ Ez → 0 ≤ Ex → 0 ≤ Dz → 0 ≤ Dx → 0 ≤ Hcoord → 0 ≤ Com →
    ‖Az - 1‖ ≤ 1 / 4 → ‖Ax - 1‖ ≤ 1 / 2 → a * Real.sqrt Ez ≤ 1 / 2 →
    c = d.comp Ax → ‖c‖ ≤ Mconst →
    (SobolevSpace.toLp μ hX.quadratic eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ)) →
    (∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hX.quadratic Ω (U b))‖ ≤ Hcoord * ‖b‖) →
    (∀ᵐ x ∂μ.restrict Ω, localGamma μ hX.quadratic fz fz x ≤ Cf ^ 2) →
    (∀ᵐ x ∂μ.restrict Ω, localGamma μ hX.quadratic (fz - fx) (fz - fx) x ≤ Cv ^ 2) →
    (∀ b, SobolevSpace.toLp μ hX.quadratic (Gz b) =ᵐ[μ.restrict Ω] localGamma μ hX.quadratic fz (U b)) →
    (∀ b, SobolevSpace.toLp μ hX.quadratic (Gx b) =ᵐ[μ.restrict Ω] localGamma μ hX.quadratic fx (U b)) →
    (∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hX.quadratic Ω
      (Gz b - U (Az b)))‖ ^ 2 ≤ Ez * ‖b‖ ^ 2) →
    (∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hX.quadratic Ω
      (Gx b - U (Ax b) + c b • eta))‖ ^ 2 ≤ Ex * ‖b‖ ^ 2) →
    (∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic
      (Gz b - U (Az b)) (Gz b - U (Az b)) x ∂μ) ≤ Dz * ‖b‖ ^ 2) →
    (∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω, localGamma μ hX.quadratic
      (Gx b - U (Ax b) + c b • eta) (Gx b - U (Ax b) + c b • eta) x ∂μ) ≤ Dx * ‖b‖ ^ 2) →
    (∀ b, (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hX.quadratic (fz - fx) (Gz b) x -
        localGamma μ hX.quadratic fz ((Gz - Gx) b) x -
        localGamma μ hX.quadratic (fz - fx) (U b) x) ^ 2 ∂μ) ≤ Com * ‖b‖ ^ 2) →
    ‖Az - Ax‖ ≤ 2 * a * e ∧ ‖c.comp (Az - 1)‖ ≤ 2 * Cm * e ∧
    ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hX.quadratic Ω
      ((Gz - Gx) b - d b • eta))‖ ≤
      (Real.sqrt (2 * Ez + 2 * Ex) + Hcoord * (2 * a * e) +
        2 * (2 * Cm * e + Mconst * (2 * a * e))) * ‖b‖ := by
  obtain ⟨Cg, Cm, hCg, hCm, hrecovery⟩ := two_center_affine_recovery hgradient hmean hn hκ
  refine ⟨Cg, Cm, hCg, hCm, ?_⟩
  intro p R hR hcurv u V N hN hu hV hVp hrep eta fz fx Gz Gx Az Ax c d
    Cf Cv Ez Ex Dz Dx Hcoord Mconst Com μ U Ω hfin a e
    hCf hCv hEz hEx hDz hDx hHcoord hCom hAz hAx hsmall hc hMc heta
    hU hf hv hGz hGx hzv hxv hze hxe hcomm
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have htotal : 0 ≤ e + Real.sqrt Ez * ‖Az - Ax‖ := by positivity
  have herr (b : Euclidean n) := two_center_affine_commutator_bound μ hX.quadratic Ω hfin
    fz fx eta hCf hCv hEz hEx hDz hDx hCom hf hv heta U Gz Gx hGz hGx Az Ax c
    hzv hxv hze hxe hcomm b
  obtain ⟨hB, hconst⟩ := hrecovery p R hR hcurv u V N hN hu hV hVp hrep eta heta
    Az (Az - Ax) c (e + Real.sqrt Ez * ‖Az - Ax‖) htotal hAz herr
  have hB' : ‖Az - Ax‖ ≤ a * (e + Real.sqrt Ez * ‖Az - Ax‖) := by
    convert hB using 1
    dsimp only [a]
    ring
  have habsorb : ‖Az - Ax‖ ≤ 2 * a * e := by
    have hh := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (Az - Ax))
    nlinarith only [hB', hh]
  have hconst' : ‖c.comp (Az - 1)‖ ≤ 2 * Cm * e := by
    have hE := mul_le_mul_of_nonneg_right hsmall he
    have hBmul := mul_le_mul_of_nonneg_left habsorb (Real.sqrt_nonneg Ez)
    have hmul : Real.sqrt Ez * ‖Az - Ax‖ ≤ e := by nlinarith only [hE, hBmul]
    exact hconst.trans ((mul_le_mul_of_nonneg_left (by linarith :
      e + Real.sqrt Ez * ‖Az - Ax‖ ≤ 2 * e) (by linarith : 0 ≤ Cm)).trans_eq (by ring))
  refine ⟨habsorb, hconst', ?_⟩
  intro b
  apply normalized_two_center_direction_error μ hX.quadratic Ω hfin
    (ne_of_gt (hX.fullSupport p R hR)) eta heta U (Gz - Gx) Ax Az c d hHcoord
    hAx hc hU ?_ habsorb hMc hconst' b
  intro v
  exact norm_le_sqrt_mul_of_sq_le _ (by positivity) (norm_nonneg v)
    (two_center_radial_fit_bounds μ hX.quadratic Ω hfin eta U Gz Gx Az Ax c hzv hxv hze hxe v).1

end RegularPointCoordinates

end

end OAI
