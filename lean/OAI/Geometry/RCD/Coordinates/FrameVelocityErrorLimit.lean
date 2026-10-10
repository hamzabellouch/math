import OAI.Geometry.RCD.Coordinates.FrameVelocityError
import OAI.Geometry.RCD.Coordinates.NormalizedL2ProductError

namespace OAI

/-! # Vanishing normalized velocity errors from the original spatial estimates -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem frame_velocity_error_tendsto {n : ℕ}
    (u : ℕ → Fin n → SobolevSpace μ hQ) (g : ℕ → SobolevSpace μ hQ)
    (S : ℕ → Set X) (hfin : ∀ k, μ (S k)≠⊤) (hpos : ∀ k, 0<μ.real (S k)) {L : ℝ}
    (hu : ∀ k i, ∀ᵐ x ∂μ.restrict (S k), localGamma μ hQ (u k i) (u k i) x≤4)
    (hg : ∀ k, ∀ᵐ x ∂μ.restrict (S k), localGamma μ hQ (g k) (g k) x≤L^2)
    (hEsq : ∀ k, IntegrableOn (fun x => (frameEnergyError μ hQ (u k) (g k) x)^2) (S k) μ)
    (hE0 : Tendsto (fun k => (μ.real (S k))⁻¹*
      ∫ x in S k, (frameEnergyError μ hQ (u k) (g k) x)^2 ∂μ) atTop (𝓝 0))
    (hD0 : Tendsto (fun k => (μ.real (S k))⁻¹*
      ∫ x in S k, gramDefect μ hQ (u k) x ∂μ) atTop (𝓝 0)) :
    (∀ k, IntegrableOn (frameVelocityError μ hQ (u k) (g k)) (S k) μ) ∧
    Tendsto (fun k => (μ.real (S k))⁻¹*
      ∫ x in S k, frameVelocityError μ hQ (u k) (g k) x ∂μ) atTop (𝓝 0) := by
  let ν (k : ℕ) := μ.restrict (S k)
  let : ∀ k, IsFiniteMeasure (ν k) := fun k =>
    ⟨by simpa only [ν,Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr (hfin k)⟩
  have hm (k : ℕ) : 0<(ν k).real univ := by
    simpa only [ν,Measure.real,Measure.restrict_apply_univ] using hpos k
  have hmem (k : ℕ) : MemLp (fun x => |frameEnergyError μ hQ (u k) (g k) x|) 2 (ν k) := by
    have hm : AEStronglyMeasurable (frameEnergyError μ hQ (u k) (g k)) (ν k) :=
      (frameEnergyError_aestronglyMeasurable μ hQ (u k) (g k)).restrict
    have habs : AEStronglyMeasurable (fun x => |frameEnergyError μ hQ (u k) (g k) x|) (ν k) := by
      simpa only [Real.norm_eq_abs] using hm.norm
    apply (memLp_two_iff_integrable_sq habs).mpr
    simpa only [sq_abs,ν,IntegrableOn] using hEsq k
  have hEabs0 : Tendsto (fun k => (μ.real (S k))⁻¹*
      ∫ x in S k, |frameEnergyError μ hQ (u k) (g k) x| ∂μ) atTop (𝓝 0) := by
    have hh := normalized_l2_product_error_tendsto ν hm
      (fun k x => |frameEnergyError μ hQ (u k) (g k) x|) (fun _ _ => 1)
      hmem (fun _ => aestronglyMeasurable_const) (C := 1)
      (Eventually.of_forall (fun _ => Eventually.of_forall (fun _ => by norm_num)))
      (by simpa only [ν,Measure.real,Measure.restrict_apply_univ,sq_abs] using hE0)
    simpa only [ν,Measure.real,Measure.restrict_apply_univ,mul_one] using hh
  have hdata (k : ℕ) := frame_velocity_error_integral μ hQ (u k) (g k) (hfin k) (hu k) (hg k)
    ((hmem k).integrable (by norm_num))
  refine ⟨fun k => (hdata k).1,?_⟩
  have hup (k : ℕ) : (μ.real (S k))⁻¹*(∫ x in S k, frameVelocityError μ hQ (u k) (g k) x ∂μ)≤
      (μ.real (S k))⁻¹*(∫ x in S k, |frameEnergyError μ hQ (u k) (g k) x| ∂μ)+
      (4*(n:ℝ)*L^2)*((μ.real (S k))⁻¹*∫ x in S k, gramDefect μ hQ (u k) x ∂μ) := by
    have hh := mul_le_mul_of_nonneg_left (hdata k).2 (inv_nonneg.mpr (hpos k).le)
    convert hh using 1
    ring
  apply squeeze_zero (fun k => mul_nonneg (inv_nonneg.mpr (hpos k).le)
    (integral_nonneg (frameVelocityError_nonneg μ hQ (u k) (g k)))) hup
  simpa only [mul_zero,add_zero] using hEabs0.add (hD0.const_mul (4*(n:ℝ)*L^2))

end RegularPointCoordinates

end

end OAI
