import OAI.Analysis.LipschitzHilbert.Fourier.LineCommutatorDerivative

namespace OAI

/-! Self-adjoint low-pass projections and the product pairing used in
the actual smooth Carleson synthesis estimate. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProjection_inner (q : SchwartzMap ℝ ℂ)
    (hq : ∀ eta, conj (q eta)=q eta) (W : ℝ) (hW : W≠0) (f g : SchwartzMap ℝ ℂ) :
    inner ℂ ((lineSchwartzProjection q W hW f).toLp 2 volume) (g.toLp 2 volume)=
      inner ℂ (f.toLp 2 volume) ((lineSchwartzProjection q W hW g).toLp 2 volume) := by
  calc
    _ = ∫ x, inner ℂ (lineSchwartzProjection q W hW f x) (g x) :=
      memLp_inner_integral volume _ _ ((lineSchwartzProjection q W hW f).memLp 2 volume) (g.memLp 2 volume)
    _ = ∫ eta, inner ℂ ((𝓕 (lineSchwartzProjection q W hW f) : SchwartzMap ℝ ℂ) eta)
        ((𝓕 g : SchwartzMap ℝ ℂ) eta) := (SchwartzMap.integral_inner_fourier_fourier _ _).symm
    _ = ∫ eta, inner ℂ ((𝓕 f : SchwartzMap ℝ ℂ) eta)
        ((𝓕 (lineSchwartzProjection q W hW g) : SchwartzMap ℝ ℂ) eta) := by
      apply integral_congr_ae
      filter_upwards [] with eta
      simp only [lineSchwartzProjection_fourier,RCLike.inner_apply,map_mul,hq]
      ring
    _ = ∫ x, inner ℂ (f x) (lineSchwartzProjection q W hW g x) :=
      SchwartzMap.integral_inner_fourier_fourier _ _
    _ = _ := (memLp_inner_integral volume _ _ (f.memLp 2 volume)
      ((lineSchwartzProjection q W hW g).memLp 2 volume)).symm

theorem reassemblyLow_conj (eta : ℝ) : conj (reassemblyLow eta)=reassemblyLow eta := by
  simp only [reassemblyLow_apply,Complex.conj_ofReal]

theorem lineLowpass_absorb (f : SchwartzMap ℝ ℂ) (W : ℝ) (hW : W≠0)
    (hband : ∀ eta, (𝓕 f : SchwartzMap ℝ ℂ) eta≠0 → |W*eta|≤1) :
    lineSchwartzProjection reassemblyLow W hW f=f := by
  apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
  ext eta
  change (𝓕 (lineSchwartzProjection reassemblyLow W hW f)) eta=(𝓕 f) eta
  rw [lineSchwartzProjection_fourier]
  by_cases hz : (𝓕 f : SchwartzMap ℝ ℂ) eta=0
  · rw [hz,mul_zero]
  · rw [reassemblyLow_one _ (hband eta hz),one_mul]

theorem lineSchwartzProduct_inner_bound (p g f : SchwartzMap ℝ ℂ) :
    ‖inner ℂ ((lineSchwartzProduct p g).toLp 2 volume) (f.toLp 2 volume)‖≤
      ‖g.toLp 2 volume‖*Real.sqrt (∫ x, ‖lineSchwartzProduct p f x‖^2) := by
  let q : ℝ → ℂ := fun x => conj (p x)*f x
  have hqnorm (x : ℝ) : ‖q x‖=‖lineSchwartzProduct p f x‖ := by
    simp only [q,lineSchwartzProduct_apply,norm_mul,RCLike.norm_conj]
  have hq : MemLp q 2 volume := ((lineSchwartzProduct p f).memLp 2 volume).of_le
    (by dsimp [q]; fun_prop) (Filter.Eventually.of_forall fun x => (hqnorm x).le)
  have he : inner ℂ ((lineSchwartzProduct p g).toLp 2 volume) (f.toLp 2 volume)=
      inner ℂ (g.toLp 2 volume) (hq.toLp q) := by
    calc
      _ = ∫ x, inner ℂ (lineSchwartzProduct p g x) (f x) :=
        memLp_inner_integral volume _ _ ((lineSchwartzProduct p g).memLp 2 volume) (f.memLp 2 volume)
      _ = ∫ x, inner ℂ (g x) (q x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [lineSchwartzProduct_apply,RCLike.inner_apply,map_mul,q]
        ring
      _ = _ := (memLp_inner_integral volume _ _ (g.memLp 2 volume) hq).symm
  have hnorm : ‖hq.toLp q‖=Real.sqrt (∫ x, ‖lineSchwartzProduct p f x‖^2) := by
    have hh := memLp_toL2_norm_sq volume q hq
    simp_rw [hqnorm] at hh
    rw [←hh,Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  simpa only [hnorm] using norm_inner_le_norm (𝕜:=ℂ) (g.toLp 2 volume) (hq.toLp q)

end LipschitzHilbert.PacketRepresentation

end

end OAI
