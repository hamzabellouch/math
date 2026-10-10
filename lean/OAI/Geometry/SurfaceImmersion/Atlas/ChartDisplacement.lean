import OAI.Geometry.SurfaceImmersion.Atlas.ChartFullLinearization

namespace OAI

/-! Real displacements and tensor targets transported through a permitted
phase chart, with their actual support and size estimates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (φ : SmallModes.Base → ℝ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x)

include hphase in
lemma chart_displacement_eq_indicator (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    QuadraticMean.displacement τ φ (chartPull e he K hK Z) =
      e.source.indicator (RealModes.realOsc τ Z ∘ e) := by
  funext x
  by_cases hx : x ∈ e.source
  · rw [Set.indicator_of_mem hx]
    change QuadraticMean.displacement τ φ (chartPull e he K hK Z) x = RealModes.realOsc τ Z (e x)
    have hh := chart_displacement_pull e he K hK φ hphase τ Z (e.map_source hx)
    simpa only [e.left_inv hx] using hh
  · rw [Set.indicator_of_notMem hx]
    apply RealModes.displacement_zero_value
    rw [chartPull_apply, Set.indicator_of_notMem hx]

lemma chart_displacement_smooth_support (hφ : ContDiff ℝ ∞ φ) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    ContDiff ℝ ∞ (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ∧
      tsupport (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) ⊆ K := by
  refine ⟨contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn
    (chartPull e he K hK Z).contDiff.contDiffOn τ), ?_⟩
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  exact hx (RealModes.displacement_zero_value τ φ ((chartPull e he K hK Z).zero_on_compl hn))

include hphase in
lemma chart_displacement_bound {s : ℝ≥0} {τ C J : ℝ} {m : ℕ}
    (_hs : 0 < (s : ℝ)) (hτ : 0 < τ) (hτs : τ ≤ s) (hτ1 : τ ≤ 1)
    (hC : 0 ≤ C) (hJ : 1 ≤ J)
    (hcoords : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    (hZ : supportedWeightedSeminorm (chartSupport e K hK) s m Z ≤ C) :
    WeightedBound Set.univ τ m ((m.factorial : ℝ) * (2 ^ m * C) * J ^ m)
      (QuadraticMean.displacement τ φ (chartPull e he K hK Z)) := by
  have hr := RealModes.weighted_realOsc isOpen_univ hτ hτs hC Z.contDiff.contDiffOn
    ((weightedBound_of_supportedSeminorm s m Z).mono_const hZ)
  have hrs : ContDiffOn ℝ ∞ (RealModes.realOsc τ Z) e.target :=
    RealModes.contDiffOn_realOsc Z.contDiff.contDiffOn τ
  have hc := (hr.restrict_open e.open_target).comp_coordinates e.open_source.uniqueDiffOn
    e.open_target.uniqueDiffOn hτ hτ1 hJ (by positivity) he hrs (fun _ hx => e.map_source hx) hcoords
  have hz : ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → RealModes.realOsc τ Z (e x) = 0 := by
    intro x hx hn
    rw [RealModes.realOsc_eq_displacement]
    exact RealModes.displacement_zero_value τ Prod.fst (chartPull_zero e K hK Z x hx hn)
  rw [chart_displacement_eq_indicator e he K hK φ hphase]
  exact hc.indicator_of_support e.open_source K.isCompact.isClosed hK (by positivity) hz

include hphase in
lemma chart_forcing_realization (τ : ℝ) (f : SupportedField (F := ComplexTensor) K)
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    pullbackField e.symm y (QuadraticMean.displacement τ φ f (e.symm y)) =
      RealModes.realOsc τ (tensorChartPush e hi K hK f) y := by
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  rw [RealModes.realOsc_eq_displacement]
  change pullbackField e.symm y (QuadraticMean.realMode (φ (e.symm y) / τ) (f (e.symm y))) =
    QuadraticMean.realMode (y.1 / τ) (tensorChartPush e hi K hK f y)
  rw [tensorChartPush_apply, Set.indicator_of_mem hy, ← hp]
  exact (realMode_complexPullback (fderiv ℝ e.symm y) _ _).symm

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
