import OAI.Geometry.RCD.Coordinates.HarmonicGlobalFrameDefect

namespace OAI

/-! # Integrable quantitative errors for a bounded-gradient probe -/

open Set Filter MeasureTheory Finset
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def frameEnergyError {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (g : SobolevSpace μ hQ) (x : X) : ℝ :=
  localGamma μ hQ g g x-∑ i, (localGamma μ hQ (u i) g x)^2

omit [ProperSpace X] in
theorem frameEnergyError_aestronglyMeasurable {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) :
    AEStronglyMeasurable (frameEnergyError μ hQ u g) μ :=
  (localGamma_memL1 μ hQ g g).aestronglyMeasurable.sub
    (univ.aestronglyMeasurable_fun_sum (fun i _ =>
      (localGamma_memL1 μ hQ (u i) g).aestronglyMeasurable.pow 2))

omit [ProperSpace X] in
theorem frame_energy_error_sq_integral {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) {S : Set X}
    (hfin : μ S≠⊤) {L : ℝ}
    (hg : ∀ᵐ x ∂μ.restrict S, localGamma μ hQ g g x≤L^2)
    (hframe : ∀ᵐ x ∂μ.restrict S, (frameEnergyError μ hQ u g x)^2≤
      frameDefectConstant n*gramDefect μ hQ u x*(localGamma μ hQ g g x)^2) :
    IntegrableOn (fun x => (frameEnergyError μ hQ u g x)^2) S μ ∧
      (∫ x in S, (frameEnergyError μ hQ u g x)^2 ∂μ)≤
        frameDefectConstant n*L^4*(∫ x in S, gramDefect μ hQ u x ∂μ) := by
  have hC : 0≤frameDefectConstant n := by unfold frameDefectConstant; positivity
  have hbound : ∀ᵐ x ∂μ.restrict S, (frameEnergyError μ hQ u g x)^2≤
      (frameDefectConstant n*L^4)*gramDefect μ hQ u x := by
    filter_upwards [hframe,hg,ae_restrict_of_ae (localGamma_self μ hQ g)] with x hx hgx he
    have hgg : 0≤localGamma μ hQ g g x := by rw [he]; positivity
    have hs : (localGamma μ hQ g g x)^2≤L^4 := by
      have hh := pow_le_pow_left₀ hgg hgx 2
      simpa only [← pow_mul] using hh
    have hh := mul_le_mul_of_nonneg_left hs (mul_nonneg hC (gramDefect_nonneg μ hQ u x))
    nlinarith only [hx,hh]
  have hdom : IntegrableOn (fun x => (frameDefectConstant n*L^4)*gramDefect μ hQ u x) S μ :=
    (gramDefect_integrableOn μ hQ u hfin).const_mul _
  have hint : IntegrableOn (fun x => (frameEnergyError μ hQ u g x)^2) S μ :=
    hdom.mono' ((frameEnergyError_aestronglyMeasurable μ hQ u g).restrict.pow 2)
      (hbound.mono (fun x hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (frameEnergyError μ hQ u g x))] using hx))
  refine ⟨hint,?_⟩
  have hh := integral_mono_ae hint hdom hbound
  simpa only [integral_const_mul] using hh

end RegularPointCoordinates

end

end OAI
