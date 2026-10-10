import OAI.Geometry.RCD.Coordinates.FrameCoefficientExcess
import OAI.Geometry.RCD.Coordinates.ACCoordinateEndpointEnergy

namespace OAI

/-! # The scalar endpoint estimate for the actual frame coefficients -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
theorem frame_path_coefficient_norm_bound {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (g : SobolevSpace μ Q) (γ : C(Time,X)) (b : Fin n → ℝ → ℝ) {L : ℝ}
    (hb : ∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun t => localGamma μ Q (u i) g (geodesicExtension γ t))
    (hg : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      localGamma μ Q g g (geodesicExtension γ t)≤L^2) :
    ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      ‖(WithLp.toLp 2 (fun i => b i t) : Euclidean n)‖^2≤
        L^2+frameVelocityError μ Q u g (geodesicExtension γ t) := by
  filter_upwards [ae_all_iff.mpr hb,hg] with t hb hg
  have he : (WithLp.toLp 2 (fun i => b i t) : Euclidean n)=
      gradientFrameCoefficients μ Q u g (geodesicExtension γ t) := by
    apply PiLp.ext
    intro i
    exact hb i
  rw [he]
  exact (frame_coefficients_velocity_error_le μ Q u g _).trans (add_le_add hg le_rfl)

omit [ProperSpace X] in
theorem frame_path_endpoint_energy {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (g : SobolevSpace μ Q) (γ : C(Time,X)) (b c : Fin n → ℝ → ℝ) (f : ℝ → ℝ)
    {L D η : ℝ}
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hb : ∀ i, AbsolutelyContinuousOnInterval (b i) 0 1)
    (hc : ∀ i, AbsolutelyContinuousOnInterval (c i) 0 1)
    (haff : ∀ i t, t∈Icc (0:ℝ) 1 → |c i t-((1-t)*c i 0+t*c i 1)|≤η)
    (hD : 0≤D)
    (hbrep : ∀ i, b i =ᵐ[volume.restrict (Icc (0:ℝ) 1)]
      fun t => localGamma μ Q (u i) g (geodesicExtension γ t))
    (hg : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      localGamma μ Q g g (geodesicExtension γ t)≤L^2)
    (hEI : IntegrableOn (fun t => frameVelocityError μ Q u g (geodesicExtension γ t)) (Icc (0:ℝ) 1))
    (hd : ∀ᵐ t : ℝ, t∈Ioo (0:ℝ) 1 →
      (deriv f t-∑ i, b i t*deriv (c i) t)^2≤D^2*frameVelocityError μ Q u g (geodesicExtension γ t)) :
    let e := ∫ t in Icc (0:ℝ) 1, frameVelocityError μ Q u g (geodesicExtension γ t)
    |f 1-f 0|≤Real.sqrt (L^2+e)*‖(WithLp.toLp 2 (fun i => c i 1-c i 0) : Euclidean n)‖+
      η*(∑ i, ∫ t in Icc (0:ℝ) 1, |deriv (b i) t|)+D*Real.sqrt e := by
  apply ac_coordinate_endpoint_energy hf hb hc haff hD
    (fun t => frameVelocityError μ Q u g (geodesicExtension γ t))
    (fun _ => frameVelocityError_nonneg μ Q u g _) hEI
    (frame_path_coefficient_norm_bound μ Q u g γ b hbrep hg)
    (fun t => frameVelocityError μ Q u g (geodesicExtension γ t))
    (fun _ => frameVelocityError_nonneg μ Q u g _) hEI hd

end RegularPointCoordinates

end

end OAI
