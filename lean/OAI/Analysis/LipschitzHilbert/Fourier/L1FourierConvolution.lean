import OAI.Analysis.LipschitzHilbert.Packets.FactoredMultiplierPackets

namespace OAI

/-! Fourier multiplication by a Schwartz kernel is convolution for every
L1 input. This includes the measurable amplitude slices used after binning. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_l1_bound (f : ℝ×ℝ → ℂ) (omega : ℝ×ℝ) :
    ‖planarFourier f omega‖≤∫ z, ‖f z‖ ∂planeMeasure := by
  unfold planarFourier
  simpa only [Circle.norm_smul] using
    norm_integral_le_integral_norm (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2)) • f z)

theorem planarFourier_l1_continuous (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) :
    Continuous (planarFourier f) := by
  unfold planarFourier
  apply continuous_of_dominated (bound:=fun z => ‖f z‖)
  · intro omega
    exact ((show Continuous (fun z : ℝ×ℝ =>
      Real.fourierChar (-(z.1*omega.1+z.2*omega.2))) by fun_prop).aestronglyMeasurable.smul
      hf.aestronglyMeasurable)
  · intro omega
    exact Filter.Eventually.of_forall (fun z => le_of_eq (Circle.norm_smul _ _))
  · exact hf.norm
  · exact Filter.Eventually.of_forall (fun z => by fun_prop)

theorem planarInverse_mul_fourier_l1 (K : SchwartzMap (ℝ×ℝ) ℂ)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure) (x : ℝ×ℝ) :
    planarInverse (fun omega => planarFourier K omega*planarFourier f omega) x=
      kernelConvolution K f x := by
  let H := fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
    (planarFourier K p.1*f p.2)*
      (Real.fourierChar ((x.1-p.2.1)*p.1.1+(x.2-p.2.2)*p.1.2):ℂ)
  have hH : Integrable H (planeMeasure.prod planeMeasure) := by
    apply ((planarFourier_integrable K).mul_prod hf).mul_bdd (c:=1)
    · exact (show Continuous (fun p : (ℝ×ℝ)×(ℝ×ℝ) =>
        (Real.fourierChar ((x.1-p.2.1)*p.1.1+(x.2-p.2.2)*p.1.2):ℂ)) by fun_prop).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun p => le_of_eq (Circle.norm_coe _))
  have hleft (omega : ℝ×ℝ) :
      Real.fourierChar (x.1*omega.1+x.2*omega.2) •
        (planarFourier K omega*planarFourier f omega)=∫ y, H (omega,y) ∂planeMeasure := by
    change Real.fourierChar (x.1*omega.1+x.2*omega.2) •
      (planarFourier K omega*(∫ y, Real.fourierChar (-(y.1*omega.1+y.2*omega.2)) • f y ∂planeMeasure))=_
    simp only [Circle.smul_def,smul_eq_mul]
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [H]
    have hphase : (x.1-y.1)*omega.1+(x.2-y.2)*omega.2=
        (x.1*omega.1+x.2*omega.2)+(-(y.1*omega.1+y.2*omega.2)) := by ring
    rw [hphase]
    simp only [Real.fourierChar.map_add_eq_mul]
    push_cast
    ring
  have hright (y : ℝ×ℝ) : (∫ omega, H (omega,y) ∂planeMeasure)=K (x-y)*f y := by
    have hinv := planarFourier_inversion K (x-y)
    change (∫ omega, (planarFourier K omega*f y)*
      (Real.fourierChar ((x.1-y.1)*omega.1+(x.2-y.2)*omega.2):ℂ) ∂planeMeasure)=_
    calc
      _ = (∫ omega, Real.fourierChar ((x.1-y.1)*omega.1+(x.2-y.2)*omega.2) •
          planarFourier K omega ∂planeMeasure)*f y := by
        rw [←integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with omega
        simp only [Circle.smul_def,smul_eq_mul]
        ring
      _ = _ := by
        change planarInverse (planarFourier K) (x-y)*f y=K (x-y)*f y
        rw [hinv]
  calc
    _ = ∫ omega, ∫ y, H (omega,y) ∂planeMeasure ∂planeMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall hleft)
    _ = ∫ y, ∫ omega, H (omega,y) ∂planeMeasure ∂planeMeasure := integral_integral_swap hH
    _ = ∫ y, K (x-y)*f y ∂planeMeasure := integral_congr_ae (Filter.Eventually.of_forall hright)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact mul_comm _ _

end LipschitzHilbert.PacketRepresentation

end

end OAI
