import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinLpReconstruction

namespace OAI

/-! Self-adjointness of the real vertical bin cutoffs, first on Schwartz
functions and then on the full L2 quotient. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem verticalBin_schwartz_adjoint (W center : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    (∫ z, inner ℂ (schwartzVerticalProjection verticalBinProfile W center f z) (g z) ∂planeMeasure)=
      ∫ z, inner ℂ (f z) (schwartzVerticalProjection verticalBinProfile W center g z) ∂planeMeasure := by
  rw [←planar_integral_inner_fourier,←planar_integral_inner_fourier]
  apply integral_congr_ae
  filter_upwards [] with omega
  simp only [schwartzVerticalProjection_fourier]
  change inner ℂ (verticalBinProfile (W*(omega.2-center)) • planarFourier f omega)
      (planarFourier g omega)=
    inner ℂ (planarFourier f omega)
      (verticalBinProfile (W*(omega.2-center)) • planarFourier g omega)
  rw [inner_smul_left,inner_smul_right]
  simp only [starRingEnd_apply,verticalBinProfile_real]

theorem verticalBinLp_adjoint (K : ℕ) (W : ℝ) (hW : 0<W) (n : ℕ)
    (f g : Lp ℂ 2 planeMeasure) :
    inner ℂ (verticalBinLp K W hW n f) g=inner ℂ f (verticalBinLp K W hW n g) := by
  let P := fun f : Lp ℂ 2 planeMeasure =>
    ∀ g : Lp ℂ 2 planeMeasure,
      inner ℂ (verticalBinLp K W hW n f) g=inner ℂ f (verticalBinLp K W hW n g)
  have hd := SchwartzMap.denseRange_toLpCLM (E:=ℝ×ℝ) (F:=ℂ) (μ:=planeMeasure)
    (by norm_num : (2:ℝ≥0∞)≠⊤)
  have h : P f := by
    apply DenseRange.induction_on (p:=P) hd f
    · simp only [P,Set.ofPred_forall]
      apply isClosed_iInter
      intro g
      exact isClosed_eq ((verticalBinLp_continuous K W hW n).inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro f0
      change ∀ g : Lp ℂ 2 planeMeasure, _
      intro g0
      apply DenseRange.induction_on (p:=fun g : Lp ℂ 2 planeMeasure =>
        inner ℂ (verticalBinLp K W hW n (f0.toLp 2 planeMeasure)) g=
          inner ℂ (f0.toLp 2 planeMeasure) (verticalBinLp K W hW n g)) hd g0
      · exact isClosed_eq (continuous_const.inner continuous_id)
          (continuous_const.inner (verticalBinLp_continuous K W hW n))
      · intro g1
        simp only [SchwartzMap.toLpCLM_apply,verticalBinLp_schwartz,
          SchwartzMap.inner_toL2_toL2_eq]
        exact verticalBin_schwartz_adjoint W (verticalBinCenter K W n) f0 g1
  exact h g

end LipschitzHilbert.PacketRepresentation

end

end OAI
