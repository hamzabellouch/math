import OAI.Geometry.RCD.Coordinates.SobolevFramePathEnergy
import OAI.Geometry.RCD.Harmonic.AffineVariationSelection

namespace OAI

/-! # Actual coefficient representatives on paths with vanishing affine-variation error -/

open Set Filter MeasureTheory Finset
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem controlled_coefficient_path_selection (μ : Measure X) (Q : QuadraticCheegerEnergy μ)
    {n : ℕ} (G : ℕ → Fin n → SobolevSpace μ Q)
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ) (C : ℕ → ℝ≥0∞) (hC : ∀ k, C k≠∞)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤C k • μ)
    (hD : ∀ k, MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (π k))
    (r : ℕ → ℝ)
    (hspeed : ∀ k, ∀ᵐ γ ∂π k, dist (γ 0) (γ 1)≤r k)
    (Ω : ℕ → Set X) (hstay : ∀ k (t : Time), ∀ᵐ x ∂(π k).map (fun γ => γ t), x∈Ω k)
    {M : ℝ} (henergy : ∀ k, (n:ℝ)*(r k)^2*(C k).toReal*
      (∑ i, ∫ x in Ω k, localGamma μ Q (G k i) (G k i) x ∂μ)≤M)
    (F : ℕ → Fin n → C(Time,X) → C(Time,ℝ))
    (hFI : ∀ k i, Integrable (fun γ => ‖F k i γ‖) (π k))
    (hFlim : Tendsto (fun k => ∫ γ, ∑ i, ‖F k i γ‖ ∂π k) atTop (𝓝 0))
    (E : ℕ → X → ℝ) (hE : ∀ k x, 0≤E k x)
    (hEI : ∀ k, IntegrableOn (E k) (Ω k) μ)
    (hElim : Tendsto (fun k => ∫ γ, (∫ t in Icc (0:ℝ) 1,
      E k (geodesicExtension γ t)) ∂π k) atTop (𝓝 0))
    (P : ℕ → C(Time,X) → Prop) (hP : ∀ k, ∀ᵐ γ ∂π k, P k γ) :
    ∃ (γ : ℕ → C(Time,X)) (b : ℕ → Fin n → ℝ → ℝ),
      (∀ k, P k (γ k)) ∧
      (∀ k i, AbsolutelyContinuousOnInterval (b k i) 0 1) ∧
      (∀ k i, b k i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
        fun t => SobolevSpace.toLp μ Q (G k i) (geodesicExtension (γ k) t)) ∧
      Tendsto (fun k => ∑ i, ‖F k i (γ k)‖) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ t in Icc (0:ℝ) 1, E k (geodesicExtension (γ k) t)) atTop (𝓝 0) ∧
      Tendsto (fun k => (∑ i, ‖F k i (γ k)‖)*
        (∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b k i) t|)) atTop (𝓝 0) := by
  let A k γ := ∑ i, ‖F k i γ‖
  let B k γ := (n:ℝ)*(r k)^2*framePathEnergy μ Q (G k) γ
  let Z k γ := ∫ t in Icc (0:ℝ) 1, E k (geodesicExtension γ t)
  have hB (k : ℕ) := compressed_frame_path_energy μ Q (G k) (π k) (hC k) (hcomp k) (hstay k)
  have hZ (k : ℕ) := compressed_segment_integral μ (π k) (hC k) (hcomp k) (hstay k)
    (hEI k) (Eventually.of_forall (hE k))
  have hBI (k : ℕ) : Integrable (B k) (π k) := (hB k).1.const_mul _
  have hBm (k : ℕ) : (∫ γ, B k γ ∂π k)≤M := by
    rw [show (∫ γ, B k γ ∂π k)=(n:ℝ)*(r k)^2*(∫ γ, framePathEnergy μ Q (G k) γ ∂π k) from
      integral_const_mul _ _]
    exact (mul_le_mul_of_nonneg_left (hB k).2 (by positivity)).trans (by
      simpa only [mul_assoc] using henergy k)
  let R k γ := ∃ b : Fin n → ℝ → ℝ,
    (∀ i, AbsolutelyContinuousOnInterval (b i) 0 1) ∧
    (∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun t => SobolevSpace.toLp μ Q (G k i) (geodesicExtension γ t)) ∧
    (∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)^2≤B k γ
  have hR (k : ℕ) : ∀ᵐ γ ∂π k, R k γ := by
    filter_upwards [sobolev_frame_variation_envelope μ Q (G k) (π k) (hgeo k) (hC k) (hcomp k) (hD k),
      hspeed k] with γ hγ hs
    obtain ⟨b,hb,_h0,_h1,he,hv⟩ := hγ
    refine ⟨b,hb,he,hv.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg hs 2) (Nat.cast_nonneg n))
      (framePathEnergy_nonneg μ Q (G k) γ)
  obtain ⟨γ,hγ,hA,hZlim,hprod⟩ := affine_variation_selection π A B Z
    (fun k γ => P k γ ∧ R k γ)
    (fun k => integrable_finsetSum _ (fun i _ => hFI k i)) hBI (fun k => (hZ k).1)
    (fun k γ => sum_nonneg (fun _ _ => norm_nonneg _))
    (fun k γ => mul_nonneg (by positivity) (framePathEnergy_nonneg μ Q (G k) γ))
    (fun k γ => integral_nonneg (fun _ => hE k _)) (fun k => (hP k).and (hR k)) hFlim hElim hBm
  choose b hb he hv using fun k => (hγ k).2
  refine ⟨γ,b,fun k => (hγ k).1,hb,he,hA,hZlim,?_⟩
  apply squeeze_zero (fun k => mul_nonneg (sum_nonneg (fun _ _ => norm_nonneg _))
    (sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _)))) _ hprod
  intro k
  apply mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (hv k))
    (sum_nonneg (fun _ _ => norm_nonneg _))

end RegularPointCoordinates

end

end OAI
