import OAI.Geometry.RCD.Coordinates.SobolevFramePlanVariation
import OAI.Geometry.RCD.Transport.CompressedSegmentIntegral

namespace OAI

/-! # An integrable envelope for the variation of the actual Sobolev coefficients -/

open Set Filter MeasureTheory Finset
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

def framePathEnergy (μ : Measure X) (Q : QuadraticCheegerEnergy μ) {n : ℕ}
    (G : Fin n → SobolevSpace μ Q) (γ : C(Time,X)) : ℝ :=
  ∑ i, ∫ t in Icc (0:ℝ) 1, |localGamma μ Q (G i) (G i) (geodesicExtension γ t)|

theorem framePathEnergy_nonneg (μ : Measure X) (Q : QuadraticCheegerEnergy μ) {n : ℕ}
    (G : Fin n → SobolevSpace μ Q) (γ : C(Time,X)) : 0≤framePathEnergy μ Q G γ :=
  sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))

theorem compressed_frame_path_energy (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (G : Fin n → SobolevSpace μ Q) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x∈Ω) :
    Integrable (framePathEnergy μ Q G) π ∧
      (∫ γ, framePathEnergy μ Q G γ ∂π)≤
        C.toReal*∑ i, ∫ x in Ω, localGamma μ Q (G i) (G i) x ∂μ := by
  have hh (i : Fin n) := compressed_segment_integral μ π hC hcomp hstay
    (localGamma_memL1 μ Q (G i) (G i)).abs.integrableOn
    (Eventually.of_forall (fun _ => abs_nonneg _))
  refine ⟨integrable_finsetSum _ (fun i _ => (hh i).1),?_⟩
  rw [show (∫ γ, framePathEnergy μ Q G γ ∂π)=
    ∑ i, ∫ γ, (∫ t in Icc (0:ℝ) 1, |localGamma μ Q (G i) (G i) (geodesicExtension γ t)|) ∂π from
      integral_finsetSum _ (fun i _ => (hh i).1),mul_sum]
  apply sum_le_sum
  intro i _
  have he : (∫ x in Ω, |localGamma μ Q (G i) (G i) x| ∂μ)=
      ∫ x in Ω, localGamma μ Q (G i) (G i) x ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (localGamma_self μ Q (G i))] with x hx
    rw [hx,abs_of_nonneg (sq_nonneg _)]
  simpa only [he] using (hh i).2.2

theorem sobolev_frame_variation_envelope (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (G : Fin n → SobolevSpace μ Q)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    ∀ᵐ γ ∂π, ∃ b : Fin n → ℝ → ℝ,
      (∀ i, AbsolutelyContinuousOnInterval (b i) 0 1) ∧
      (∀ i, b i 0=SobolevSpace.toLp μ Q (G i) (γ 0)) ∧
      (∀ i, b i 1=SobolevSpace.toLp μ Q (G i) (γ 1)) ∧
      (∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
        fun t => SobolevSpace.toLp μ Q (G i) (geodesicExtension γ t)) ∧
      (∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)^2≤
        (n:ℝ)*(dist (γ 0) (γ 1))^2*framePathEnergy μ Q G γ := by
  filter_upwards [sobolev_frame_plan_variation μ Q G π hgeo hC hcomp hD] with γ hγ
  obtain ⟨b,hb,h0,h1,he,hvar⟩ := hγ
  refine ⟨b,hb,h0,h1,he,hvar.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _))
  exact sum_le_sum (fun i _ => (le_abs_self _).trans abs_integral_le_integral_abs)

end RegularPointCoordinates

end

end OAI
