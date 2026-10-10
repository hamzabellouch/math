import OAI.Geometry.SurfaceImmersion.Correction.UnperturbedFreeModeIdentity
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLocalMeanProfile
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanData

namespace OAI

/-! Polynomial bounds for the actual charted metric mean, with no
polynomial differential perturbation. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    {c : PolynomialSolveData P 0 G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

lemma mean_unperturbed (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (hs : 0 < (s : ℝ)) (δ : ℝ) (q : ℕ) {f : SmallModes.Base → Tensor}
    (hf : ContDiffOn ℝ ∞ f c.e.source) (hball : InTrialBall c.e.source reference r f) :
    d.mean hρ δ q f = c.e.source.indicator
      (meanTerm δ s c.realMap d.cutoff d.form c.e c.e.symm q (τ/s) f) := by
  have hamp : (d.amplitude hρ f : SmallModes.Base → ℝ) =
      phaseAmplitude d.cutoff (coefficient d.form c.e.symm f) :=
    funext (c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hf hball)
  funext x
  rw [mean, c.combinedMeanField_unperturbed]
  simp only [hamp]
  apply congrArg (fun a : SmallModes.Base → Tensor => c.e.source.indicator a x)
  funext y
  simp only [meanTerm, div_mul_cancel₀ τ hs.ne']

end ChartedMeanData

/-- The exponent and coefficient are uniform over the actual solver data;
only its explicitly supplied geometric profile varies. -/
theorem polynomial_charted_metric_mean (q : ℕ) :
    ∃ (p : ℕ → ℕ) (C : ℕ → ℝ), (∀ m, 1 ≤ C m) ∧
    ∀ {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
      {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
      {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P 0 G hG φ K τ s)
      {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) →
      (∀ m, ρ⁻¹ ≤ J m ∧ d.budgets.inv (m+q+2) ≤ J m ∧
        d.budgets.forms (m+q+2) ≤ J m ∧ d.budgets.psi (m+q+2) ≤ J m ∧
        d.budgets.mode (m+q+2) ≤ J m ∧ d.budgets.normal (m+q+2) ≤ J m ∧
        d.budgets.chi m ≤ J m ∧ d.budgets.pull m ≤ J m) →
      ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s reference r (q+2) (rescaledMean (τ/s) (d.mean hρ δ q))
        (polynomialMeanProfile p C J) (polynomialMeanProfile p C J) := by
  obtain ⟨p,C,hC,hm⟩ := polynomial_local_mean_majorants q
  refine ⟨p,C,hC,?_⟩
  intro n P τ G hG φ K s c r ρ R reference d hρ hτ hs hτs hs1 J hJ hbounds δ hδ
  have hη : 0 < τ/(s : ℝ) := div_pos hτ hs
  have hη1 : τ/(s : ℝ) ≤ 1 := (div_le_one₀ hs).mpr hτs
  have hl := hm d.localBounds d.budgets hs hs1 hρ J hJ hbounds δ hδ
  apply rescaledMean_bounds uniqueDiffOn_univ hη _ _ _ hl.B_pos hl.K_pos
  · intro f _ _
    exact (c.combinedMeanField δ q (d.amplitude hρ f)).contDiff.contDiffOn
  · intro m A f hA hf hball hbf
    have hfs := hf.mono (subset_univ c.e.source)
    have hb := fun x (_hx : x ∈ c.e.source) => hball x (mem_univ x)
    have hv := hl.value _ hη hη1 m A f hA hfs hb (hbf.restrict_open c.e.open_source)
    have heq := d.mean_unperturbed hρ hs δ q hfs hb
    have hv' : WeightedBound c.e.source s m ((τ/s)*polynomialMeanProfile p C J m A)
        (d.mean hρ δ q f) := by
      rw [heq]
      exact hv.congr (fun x hx => indicator_of_mem hx _)
    apply hv'.extend_support c.e.open_source
      ((c.combinedMeanField δ q (d.amplitude hρ f)).tsupport_subset.trans c.supportChart)
    exact mul_nonneg hη.le (zero_le_one.trans (hl.B_pos m A hA))
  · intro m A D f g hA hD hf hg hballf hballg hbf hbg hbd
    have hfs := hf.mono (subset_univ c.e.source)
    have hgs := hg.mono (subset_univ c.e.source)
    have hballf' := fun x (_hx : x ∈ c.e.source) => hballf x (mem_univ x)
    have hballg' := fun x (_hx : x ∈ c.e.source) => hballg x (mem_univ x)
    have hv := hl.difference _ hη hη1 m A D f g hA hD hfs hgs hballf' hballg'
      (hbf.restrict_open c.e.open_source) (hbg.restrict_open c.e.open_source)
      (hbd.restrict_open c.e.open_source)
    have heqf := d.mean_unperturbed hρ hs δ q hfs hballf'
    have heqg := d.mean_unperturbed hρ hs δ q hgs hballg'
    have hv' : WeightedBound c.e.source s m (polynomialMeanProfile p C J m A*(τ/s)*D)
        (d.mean hρ δ q f-d.mean hρ δ q g) := by
      rw [heqf, heqg]
      exact hv.congr (fun x hx => by simp only [Pi.sub_apply, indicator_of_mem hx])
    have hsupport : tsupport (d.mean hρ δ q f-d.mean hρ δ q g) ⊆ c.e.source :=
      (tsupport_sub _ _).trans (union_subset
        ((c.combinedMeanField δ q (d.amplitude hρ f)).tsupport_subset.trans c.supportChart)
        ((c.combinedMeanField δ q (d.amplitude hρ g)).tsupport_subset.trans c.supportChart))
    exact hv'.extend_support c.e.open_source hsupport
      (mul_nonneg (mul_nonneg (zero_le_one.trans (hl.K_pos m A hA)) hη.le) hD)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
