import OAI.Geometry.RCD.Sobolev.SupportedWeakSourceBound

namespace OAI

/-! # The local Hamilton--Jacobi equation against a Laplacian test

Self-adjointness moves the viscosity source onto the fixed compact test.
All pairings retain the actual local Sobolev representative.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem weak_laplacian_transpose (w φ : SobolevSpace μ Q) (q ξ : Lp ℝ 2 μ)
    (hq : IsWeakLaplacian μ Q w q) (hξ : IsWeakLaplacian μ Q φ ξ) :
    inner ℝ q (SobolevSpace.toLp μ Q φ) = inner ℝ ξ (SobolevSpace.toLp μ Q w) := by
  have h₁ := hq φ
  have h₂ := hξ w
  rw [energyForm_comm μ Q] at h₁
  linarith

omit [ProperSpace X] in
theorem local_hamilton_jacobi_test_pairing
    (w φ : SobolevSpace μ Q) (q ξ : Lp ℝ 2 μ)
    (hq : IsWeakLaplacian μ Q w q) (hξ : IsWeakLaplacian μ Q φ ξ)
    {Ω : Set X} (H D : X → ℝ) (ε : ℝ)
    (hw : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] H)
    (hD : D =ᵐ[μ.restrict Ω] fun x => ε/2*q x + localGamma μ Q w w x/2)
    (hφs : ∀ᵐ x ∂μ, x ∉ Ω → SobolevSpace.toLp μ Q φ x = 0)
    (hξs : ∀ᵐ x ∂μ, x ∉ Ω → ξ x = 0)
    {B : ℝ} (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q φ x| ≤ B) :
    (∫ x in Ω, SobolevSpace.toLp μ Q φ x * localGamma μ Q w w x ∂μ) =
      2*(∫ x in Ω, SobolevSpace.toLp μ Q φ x * D x ∂μ) -
      ε*(∫ x in Ω, ξ x * H x ∂μ) := by
  let Φ := SobolevSpace.toLp μ Q φ
  let W := SobolevSpace.toLp μ Q w
  have hiq : Integrable (fun x => Φ x*q x) μ := by
    simpa only [Real.inner_apply] using (L2.integrable_inner (𝕜 := ℝ) Φ q)
  have hig : Integrable (fun x => Φ x*localGamma μ Q w w x) μ :=
    (localGamma_memL1 μ Q w w).bdd_mul (Lp.aestronglyMeasurable Φ)
      (by simpa only [Real.norm_eq_abs] using hB)
  have hpair : (∫ x in Ω, Φ x*q x ∂μ) = ∫ x in Ω, ξ x*H x ∂μ := by
    have he := weak_laplacian_transpose μ Q w φ q ξ hq hξ
    have heq : (∫ x, Φ x*q x ∂μ) = ∫ x, ξ x*W x ∂μ := by
      calc
        _ = ∫ x, q x*Φ x ∂μ := integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
        _ = _ := by simpa only [L2.inner_def,Real.inner_apply] using he
    calc
      _ = ∫ x, Φ x*q x ∂μ := setIntegral_eq_integral_of_ae_compl_eq_zero (by
        filter_upwards [hφs] with x hx hnot
        rw [hx hnot,zero_mul])
      _ = ∫ x, ξ x*W x ∂μ := heq
      _ = ∫ x in Ω, ξ x*W x ∂μ := (setIntegral_eq_integral_of_ae_compl_eq_zero (by
        filter_upwards [hξs] with x hx hnot
        rw [hx hnot,zero_mul])).symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hw] with x hx
        rw [hx])
  have hid : (∫ x in Ω, Φ x*D x ∂μ) =
      ε/2*(∫ x in Ω, Φ x*q x ∂μ) + 1/2*(∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ) := by
    calc
      _ = ∫ x in Ω, ε/2*(Φ x*q x)+1/2*(Φ x*localGamma μ Q w w x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hD] with x hx
        rw [hx]
        ring
      _ = _ := by
        rw [integral_add (hiq.integrableOn.const_mul _) (hig.integrableOn.const_mul _),
          integral_const_mul,integral_const_mul]
  change (∫ x in Ω, Φ x*localGamma μ Q w w x ∂μ) = _
  rw [hid,← hpair]
  ring

end RegularPointCoordinates

end

end OAI
