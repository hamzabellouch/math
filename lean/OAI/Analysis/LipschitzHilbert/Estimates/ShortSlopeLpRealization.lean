import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeLp

namespace OAI

/-! The actual integral realization of the continuous L2 short-time map. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def shortSlopeLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) : Lp ℂ 2 planeMeasure :=
  (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1.toLp
    (shortSlopeOperator K u f)

theorem shortSlopeLp_coe (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    (shortSlopeLp K hKm hK u hu f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] shortSlopeOperator K u f :=
  MemLp.coeFn_toLp _

theorem shortSlopeLp_toLp (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : MemLp f 2 planeMeasure) :
    shortSlopeLp K hKm hK u hu (hf.toLp f)=
      (shortSlopeOperator_energy K hKm hK u hu f hfm hf).1.toLp (shortSlopeOperator K u f) := by
  apply Lp.ext
  exact (shortSlopeLp_coe K hKm hK u hu _).trans
    ((shortSlopeOperator_congr_ae K u hu _ f (Lp.stronglyMeasurable (hf.toLp f)).measurable
      hfm hf.coeFn_toLp).trans (MemLp.coeFn_toLp _).symm)

theorem shortSlopeLp_sub (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f g : Lp ℂ 2 planeMeasure) :
    shortSlopeLp K hKm hK u hu (f-g)=shortSlopeLp K hKm hK u hu f-shortSlopeLp K hKm hK u hu g := by
  apply Lp.ext
  have hc := shortSlopeOperator_congr_ae K u hu (show Lp ℂ 2 planeMeasure from f-g)
    ((f : (ℝ×ℝ) → ℂ)-(g : (ℝ×ℝ) → ℂ)) (Lp.stronglyMeasurable (f-g)).measurable
    ((Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable) (Lp.coeFn_sub f g)
  have hs := shortSlopeOperator_sub_ae K hKm hK u hu f g (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable (Lp.memLp f) (Lp.memLp g)
  filter_upwards [shortSlopeLp_coe K hKm hK u hu (f-g),hc,hs,
    shortSlopeLp_coe K hKm hK u hu f,shortSlopeLp_coe K hKm hK u hu g,
    Lp.coeFn_sub (shortSlopeLp K hKm hK u hu f) (shortSlopeLp K hKm hK u hu g)]
    with z h1 h2 h3 h4 h5 h6
  rw [h1,h2,h3,h6]
  simp only [Pi.sub_apply,h4,h5]

theorem shortSlopeLp_norm (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    ‖shortSlopeLp K hKm hK u hu f‖≤(2*∫ t, ‖K t‖)*‖f‖ := by
  have h := (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).2
  rw [←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn,
    ←memLp_toL2_norm_sq planeMeasure _
      (shortSlopeOperator_energy K hKm hK u hu f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)).1] at h
  change ‖shortSlopeLp K hKm hK u hu f‖^2≤4*(∫ t, ‖K t‖)^2*‖f‖^2 at h
  have hn : 0≤2*∫ t, ‖K t‖ := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hn (norm_nonneg f))).mp
  calc
    _ ≤ 4*(∫ t, ‖K t‖)^2*‖f‖^2 := h
    _ = _ := by ring

theorem shortSlopeLp_continuous (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) : Continuous (shortSlopeLp K hKm hK u hu) := by
  apply LipschitzWith.continuous (K:=⟨2*∫ t, ‖K t‖,by positivity⟩)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  rw [dist_eq_norm,dist_eq_norm,←shortSlopeLp_sub]
  exact shortSlopeLp_norm K hKm hK u hu (f-g)

theorem shortL2Operator_eq_actual (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    shortL2Operator K hKm hK u hu f=shortSlopeLp K hKm hK u hu f := by
  have hd : DenseRange (fun g : SchwartzMap (ℝ×ℝ) ℂ => g.toLp 2 planeMeasure) :=
    SchwartzMap.denseRange_toLpCLM (F:=ℂ) (by norm_num : (2:ℝ≥0∞)≠⊤)
  refine hd.induction_on f ?_ ?_
  · exact isClosed_eq (shortL2Operator K hKm hK u hu).continuous (shortSlopeLp_continuous K hKm hK u hu)
  · intro g
    rw [shortL2Operator_onSchwartz]
    change shortSchwartzToL2 K hKm hK u hu g=
      shortSlopeLp K hKm hK u hu ((g.memLp 2 planeMeasure).toLp (g : (ℝ×ℝ) → ℂ))
    rw [shortSlopeLp_toLp K hKm hK u hu g g.continuous.measurable (g.memLp 2 planeMeasure)]
    rfl

theorem shortL2Operator_coe (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (f : Lp ℂ 2 planeMeasure) :
    (shortL2Operator K hKm hK u hu f : (ℝ×ℝ) → ℂ)=ᵐ[planeMeasure] shortSlopeOperator K u f := by
  rw [shortL2Operator_eq_actual]
  exact shortSlopeLp_coe K hKm hK u hu f

end LipschitzHilbert.PacketRepresentation

end

end OAI
