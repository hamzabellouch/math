import OAI.Geometry.RCD.Transport.RadialTransportEulerIdentity
import OAI.Geometry.RCD.Transport.RadialTransportGeometry
import OAI.Geometry.RCD.Transport.WeightedTransportEnergy

namespace OAI

/-! # Radial transport for the constructed cutoff and the actual weak equation -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The annular energy of the original bounded residual has a quadratic
bound from its inner norm and the two actual L2 errors. The cutoff and its
derivative are constructed, and the balance follows from the weak Laplacian. -/
theorem radial_transport_annular_energy {n : ℕ} {R a : ℝ} (hR : 2 ≤ R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z : X)
    (f w : SobolevSpace μ hQ)
    (hf : IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a)
    (C : ℝ≥0) (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (F e : X → ℝ) (hF : MemLp F 2 μ) (he : MemLp e 2 μ)
    (heuler : localGamma μ hQ f w =ᵐ[μ.restrict (ball z (4 * R))]
      fun x => SobolevSpace.toLp μ hQ w x + F x / 2)
    (hradial : localGamma μ hQ f (inwardSobolev μ hQ z (3 * R))
      =ᵐ[μ.restrict (ball z (4 * R))] fun x => e x - dist z x)
    (hsphere : μ (sphere z R) = 0) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    (∫ x in ball z (4 * R), transportEnergyWeight n R z x *
      (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
        2 * ((a + 2) * D + D / 4) * (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) +
        2 * D * (∫ x in ball z (4 * R), (F x) ^ 2 ∂μ) +
        2 * (C : ℝ) ^ 2 * Q * (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) := by
  dsimp only
  let β := transportCutoffExponent n
  let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
  let Q := R ^ (-(β + 1))
  let ν := μ.restrict (ball z (4 * R))
  let W : X → ℝ := SobolevSpace.toLp μ hQ w
  let χ := radialPowerRep β R (3 * R) z
  let ρ := transportDerivativeWeight n R z
  let ζ := transportEnergyWeight n R z
  have hR0 : 0 < R := by linarith
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hR0.le _
  have hD0 : 0 ≤ D := by
    have hh := (radialPowerRep_bounds hβ hR0 (by linarith : R ≤ 3 * R) z z).1
    rw [radialPowerRep_inner hβ hR0 (by linarith : R ≤ 3 * R) z z (by simp; linarith)] at hh
    exact hh
  let η := radialPowerTest μ hQ (inwardSobolev μ hQ z (3 * R))
    hβ hR0 (by linarith : R ≤ 3 * R)
  let Kfun := fun x => (a + 2) * χ x + localGamma μ hQ f η x
  have hχlip : LipschitzWith ⟨Q, hQ0⟩ χ := radialPowerRep_lipschitz hβ hR0 z
  have hχbd : ∀ x, 0 ≤ χ x ∧ χ x ≤ D :=
    radialPowerRep_bounds hβ hR0 (by linarith : R ≤ 3 * R) z
  have hχabs : ∀ x, |χ x| ≤ (⟨D, hD0⟩ : ℝ≥0) := fun x => by
    rw [abs_of_nonneg (hχbd x).1]
    exact (hχbd x).2
  have hη : SobolevSpace.toLp μ hQ η =ᵐ[μ] χ :=
    radialPowerTest_inward_coe μ hQ hβ hR0 (by linarith : R ≤ 3 * R) z
  have hbal := radial_transport_euler_identity μ hQ (ball z (4 * R)) isOpen_ball.measurableSet
    f w η hf C ⟨D, hD0⟩ ⟨Q, hQ0⟩ hw χ hχlip
    (radialPowerRep_compact (by linarith : R ≤ 3 * R) z)
    hχabs (fun x => (hχbd x).1)
    (radialPowerRep_tsupport (by linarith : R ≤ 3 * R) (by linarith : 3 * R < 4 * R) z)
    hη F hF heuler
  have hW : MemLp W 2 μ := Lp.memLp (SobolevSpace.toLp μ hQ w)
  have hWsq : ∀ᵐ x ∂μ, ‖(W x) ^ 2‖ ≤ (C : ℝ) ^ 2 := by
    filter_upwards [hw] with x hx
    rw [Real.norm_eq_abs, abs_pow, sq_abs]
    have hh := (sq_le_sq₀ (abs_nonneg _) C.coe_nonneg).mpr hx
    simpa only [sq_abs] using hh
  have hiχ : Integrable (fun x => χ x * (W x) ^ 2) μ :=
    hW.integrable_sq.bdd_mul hχlip.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hχabs x)
  have hK : Integrable (fun x => Kfun x * (W x) ^ 2) μ := by
    convert (hiχ.const_mul (a + 2)).add
      ((localGamma_memL1 μ hQ f η).bdd_mul (hW.aestronglyMeasurable.pow 2) hWsq) using 1
    funext x
    simp only [Kfun, Pi.add_apply, Pi.pow_apply]
    ring
  have hnot : ∀ᵐ x ∂ν, dist z x ≠ R := by
    have hh := ae_restrict_of_ae (s := ball z (4 * R)) (measure_eq_zero_iff_ae_notMem.mp hsphere)
    filter_upwards [hh] with x hx
    simpa only [mem_sphere, dist_comm] using hx
  have hgeom := hnot.mono fun x hx => radial_transport_weight_geometry hR ha han z x hx
  have hγ : localGamma μ hQ f η =ᵐ[ν] fun x =>
      ρ x * localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) x :=
    ae_restrict_of_ae (radial_transport_cutoff_gamma μ hQ n hR0 z f)
  have hcoerce : ∀ᵐ x ∂ν, ζ x ≤ (a + 2) * D * (ball z R).indicator (fun _ => (1 : ℝ)) x -
      Kfun x + ρ x * e x := by
    filter_upwards [hgeom, hγ, hradial] with x hx hg hr
    have hh := hx.2.2.2
    change localGamma μ hQ f η x = ρ x * localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) x at hg
    change ζ x ≤ _ at hh ⊢
    dsimp only [Kfun]
    rw [hg, hr]
    convert hh using 1
    dsimp only [D, β, ρ, χ]
    ring
  have hE := weighted_transport_energy ν (ball z R) isOpen_ball.measurableSet
    (hW.restrict (ball z (4 * R))) (he.restrict (ball z (4 * R))) (hF.restrict (ball z (4 * R))) hχlip.continuous.aestronglyMeasurable
    (transportDerivativeWeight_measurable n R z).aestronglyMeasurable
    (transportEnergyWeight_measurable n hR0 z).aestronglyMeasurable
    (ae_restrict_of_ae hw) (Filter.Eventually.of_forall hχbd)
    (Filter.Eventually.of_forall (transportDerivativeWeight_bounds n hR0 z))
    (hgeom.mono fun _ hx => hx.1) hK.integrableOn hcoerce
    (hgeom.mono fun _ hx => hx.2.2.1) (hgeom.mono fun _ hx => hx.2.1) hbal
  have hsub : ball z R ⊆ ball z (4 * R) := ball_subset_ball (by linarith)
  simpa only [ν, W, ζ, D, Q, β, Measure.restrict_restrict_of_subset hsub] using hE

end RegularPointCoordinates

end

end OAI
