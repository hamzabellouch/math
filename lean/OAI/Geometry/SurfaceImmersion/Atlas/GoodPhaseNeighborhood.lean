import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartGeometry

namespace OAI

/-! Compactly contained local domains for actual noncritical good phases. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma continuous_phaseDerivative {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    Continuous (phaseDerivative φ) := by
  exact ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.prodMk
    ((hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous

/-- A good phase at an immersed point has an actual smaller phase chart with
compact source and target bounds inside a larger good-mode domain. -/
theorem exists_good_phase_neighborhood {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) {p : Base}
    (hImm : Function.Injective (fderiv ℝ F p))
    (hgood : Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ (d : OpenPartialHomeomorph Base Base) (KE KV Ω : Set Base),
      p ∈ d.source ∧ (∀ x, (d x).1 = φ x) ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm ∧
      IsCompact KE ∧ IsCompact KV ∧ d.source ⊆ KE ∧ d.target ⊆ KV ∧ KV ⊆ Ω ∧
      RealModeDomain (F ∘ d.symm) Ω := by
  have hD := gramDet_ne_zero_of_injective (fderiv ℝ F p) hImm
  have hde : ∀ᶠ x in 𝓝 p,
      NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0 :=
    (continuous_gramDet_field hF).continuousAt.eventually_ne hD
  have hge := good_eventually (contDiffAt_realSecondTensor hF p hD).continuousAt
    (continuous_phaseDerivative hφ).continuousAt hgood
  obtain ⟨U,hUs,hU,hpU⟩ := mem_nhds_iff.mp (hde.and hge)
  obtain ⟨e₀,hep,hphase,he₀,hi₀⟩ := exists_extended_phase_chart hφ hgood.1
  let e := e₀.restrOpen U hU
  have hep' : p ∈ e.source := ⟨hep,hpU⟩
  have he : ContDiff ℝ ∞ e := he₀
  have hi : ContDiff ℝ ∞ e.symm := hi₀
  have hdom : RealModeDomain (F ∘ e.symm) e.target :=
    realModeDomain_smooth_phase_chart hF hφ e he hi hphase
      (fun x hx => injective_of_gramDet_ne_zero _ (hUs hx.2).1)
      (fun x hx => (hUs hx.2).2)
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp e.open_source p hep'
  let V := Metric.ball p (r/2)
  let KE := Metric.closedBall p (r/2)
  have hKE : IsCompact KE := isCompact_closedBall p (r/2)
  have hKEe : KE ⊆ e.source :=
    (Metric.closedBall_subset_ball (by linarith : r/2 < r)).trans hball
  let d := e.restrOpen V Metric.isOpen_ball
  let KV := e '' KE
  have hKV : IsCompact KV := hKE.image he.continuous
  refine ⟨d,KE,KV,e.target,?_,hphase,he,hi,hKE,hKV,?_,?_,?_,hdom⟩
  · exact ⟨hep',Metric.mem_ball_self (by linarith)⟩
  · intro x hx
    exact Metric.ball_subset_closedBall hx.2
  · intro y hy
    refine ⟨d.symm y,?_,?_⟩
    · exact Metric.ball_subset_closedBall (d.map_target hy).2
    · exact d.right_inv hy
  · rintro y ⟨x,hx,rfl⟩
    exact e.map_source (hKEe hx)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
