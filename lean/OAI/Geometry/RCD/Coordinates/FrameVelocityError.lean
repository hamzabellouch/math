import OAI.Geometry.RCD.Coordinates.FrameCoefficientBound

namespace OAI

/-! # An integrable spatial density controlling the scalar velocity error -/

open Set Filter MeasureTheory Finset
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def frameVelocityError {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (x : X) : ℝ :=
  |frameEnergyError μ hQ u g x|+gramDefect μ hQ u x*‖gradientFrameCoefficients μ hQ u g x‖^2

omit [ProperSpace X] in
theorem frameVelocityError_nonneg {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (x : X) : 0≤frameVelocityError μ hQ u g x :=
  add_nonneg (abs_nonneg _) (mul_nonneg (gramDefect_nonneg μ hQ u x) (sq_nonneg _))

theorem frame_velocity_error_integral {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) {S : Set X}
    (hfin : μ S≠⊤) {L : ℝ}
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤4)
    (hg : ∀ᵐ x ∂μ.restrict S, localGamma μ hQ g g x≤L^2)
    (hE : IntegrableOn (fun x => |frameEnergyError μ hQ u g x|) S μ) :
    IntegrableOn (frameVelocityError μ hQ u g) S μ ∧
      (∫ x in S, frameVelocityError μ hQ u g x ∂μ)≤
        (∫ x in S, |frameEnergyError μ hQ u g x| ∂μ)+
          4*(n:ℝ)*L^2*(∫ x in S, gramDefect μ hQ u x ∂μ) := by
  have hD := gramDefect_integrableOn μ hQ u hfin
  have hnm : AEStronglyMeasurable (fun x => ‖gradientFrameCoefficients μ hQ u g x‖^2) (μ.restrict S) := by
    have he : (fun x => ‖gradientFrameCoefficients μ hQ u g x‖^2)=
        fun x => ∑ i, (localGamma μ hQ (u i) g x)^2 := by
      funext x
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [he]
    exact univ.aestronglyMeasurable_fun_sum (fun i _ =>
      (localGamma_memL1 μ hQ (u i) g).aestronglyMeasurable.restrict.pow 2)
  have hbound : ∀ᵐ x ∂μ.restrict S,
      gramDefect μ hQ u x*‖gradientFrameCoefficients μ hQ u g x‖^2≤
        (4*(n:ℝ)*L^2)*gramDefect μ hQ u x := by
    filter_upwards [gradient_frame_coefficients_bounded μ hQ u g hu hg] with x hx
    nlinarith [mul_le_mul_of_nonneg_left hx (gramDefect_nonneg μ hQ u x)]
  have hdom := hD.const_mul (4*(n:ℝ)*L^2)
  have hp : IntegrableOn (fun x => gramDefect μ hQ u x*
      ‖gradientFrameCoefficients μ hQ u g x‖^2) S μ := by
    apply hdom.mono' (hD.aestronglyMeasurable.mul hnm)
    filter_upwards [hbound] with x hx
    change |gramDefect μ hQ u x*‖gradientFrameCoefficients μ hQ u g x‖^2|≤_
    rw [abs_of_nonneg (mul_nonneg (gramDefect_nonneg μ hQ u x)
      (sq_nonneg ‖gradientFrameCoefficients μ hQ u g x‖))]
    exact hx
  refine ⟨hE.add hp,?_⟩
  change (∫ x in S, |frameEnergyError μ hQ u g x|+
    gramDefect μ hQ u x*‖gradientFrameCoefficients μ hQ u g x‖^2 ∂μ)≤_
  rw [integral_add hE hp]
  have hh := integral_mono_ae hp hdom hbound
  rw [integral_const_mul] at hh
  linarith

end RegularPointCoordinates

end

end OAI
