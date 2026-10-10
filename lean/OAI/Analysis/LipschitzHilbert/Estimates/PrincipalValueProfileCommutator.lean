import OAI.Analysis.LipschitzHilbert.Fourier.VerticalConvolutionPVLimit

namespace OAI

/-! An unconditional L2 estimate for the actual principal-value/profile
commutator on a vertically band-limited input. It includes the passage to
the singular kernel, rather than assuming a bounded full PV operator. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace LipschitzHilbert.PacketRepresentation

theorem sharpVerticalCommutator_bound (q : SchwartzMap ℝ ℂ) (W center epsilon R : ℝ)
    (hW : 0<W) (he : 0<epsilon) (hR : 0<R)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (F : ℝ) (hF : 0≤F) (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤F) :
    eLpNorm (sharpVerticalCommutator q W center epsilon R u f) 2 planeMeasure≤
      ENNReal.ofReal ((2*R*Real.sqrt (verticalProfileCommutatorConstant q)*(W*F))*
        ‖f.toLp 2 planeMeasure‖) := by
  obtain ⟨hm,he2⟩ := sharpVerticalCommutator_energy q W center epsilon R hW he hR u hu f F hF hband
  rw [←memLp_toL2_norm_sq planeMeasure _ hm,
    ←memLp_toL2_norm_sq planeMeasure f (f.memLp 2 planeMeasure)] at he2
  have hn : ‖hm.toLp (sharpVerticalCommutator q W center epsilon R u f)‖≤
      (2*R*Real.sqrt (verticalProfileCommutatorConstant q)*(W*F))*‖f.toLp 2 planeMeasure‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    change ‖hm.toLp (sharpVerticalCommutator q W center epsilon R u f)‖^2≤
      4*R^2*verticalProfileCommutatorConstant q*(W*F)^2*‖f.toLp 2 planeMeasure‖^2 at he2
    apply he2.trans_eq
    simp only [mul_pow,Real.sq_sqrt (verticalProfileCommutatorConstant_nonneg q)]
    ring
  rw [←Lp.enorm_toLp hm,←ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

theorem principalValueProfileCommutator_measurable (q : SchwartzMap ℝ ℂ)
    (W center R : ℝ) (hR : 0<R) (hRsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    Measurable (principalValueProfileCommutator q W center R u f) :=
  (verticalConvolution_measurable _ (verticalProfileKernel_continuous q W center).measurable
    _ (productSlopePrincipalValue_measurable u hu f f.differentiable R hR hRsmall)).sub
    (productSlopePrincipalValue_measurable u hu _
      (schwartzVerticalProjection q W center f).differentiable R hR hRsmall)

theorem principalValueProfileCommutator_bound (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (hW : 0<W) (hR : 0<R) (hRsmall : R≤1/4)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (F : ℝ) (hF : 0≤F)
    (hband : ∀ omega, planarFourier f omega≠0 → |omega.2|≤F) :
    MemLp (principalValueProfileCommutator q W center R u f) 2 planeMeasure ∧
    eLpNorm (principalValueProfileCommutator q W center R u f) 2 planeMeasure≤
      ENNReal.ofReal ((2*R*Real.sqrt (verticalProfileCommutatorConstant q)*(W*F))*
        ‖f.toLp 2 planeMeasure‖) := by
  have hm := principalValueProfileCommutator_measurable q W center R hR hRsmall u hu.continuous.measurable f
  have hb : eLpNorm (principalValueProfileCommutator q W center R u f) 2 planeMeasure≤
      ENNReal.ofReal ((2*R*Real.sqrt (verticalProfileCommutatorConstant q)*(W*F))*
        ‖f.toLp 2 planeMeasure‖) := by
    apply Lp.eLpNorm_le_of_ae_tendsto (u:=(atTop : Filter ℕ))
      (Eventually.of_forall fun n => sharpVerticalCommutator_bound q W center (pvInnerRadius R n) R
        hW (pvInnerRadius_pos R hR n) hR u hu f F hF hband)
      (fun n => (sharpVerticalCommutator_energy q W center (pvInnerRadius R n) R hW
        (pvInnerRadius_pos R hR n) hR u hu f F hF hband).1.aestronglyMeasurable)
      hm.aestronglyMeasurable
    exact Eventually.of_forall (sharpVerticalCommutator_tendsto q W center R hW hR hRsmall
      u hu.continuous.measurable hub f)
  exact ⟨hb.trans_lt (by simp),hb⟩

end LipschitzHilbert.PacketRepresentation

end

end OAI
