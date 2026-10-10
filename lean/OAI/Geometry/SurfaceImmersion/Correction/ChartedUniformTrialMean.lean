import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanProfile
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedUniformAmplitude
import OAI.Geometry.SurfaceImmersion.Correction.ChartedUniformCombinedMean

namespace OAI

/-! The actual trial mean has majorants depending only on the fixed profile,
before choosing either oscillation scale or immersion. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

theorem uniform_charted_trial_mean {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    let L := tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
    ∃ β κ : ℝ, 1 ≤ β ∧ 1 ≤ κ ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      ∀ δ : ℝ, 0 < δ → ∀ (A B : SmallModes.Base → Tensor) (D : ℝ), 0 ≤ C → 0 ≤ D →
      ContDiffOn ℝ ∞ A c.e.source → ContDiffOn ℝ ∞ B c.e.source →
      InTrialBall c.e.source reference r A → InTrialBall c.e.source reference r B →
      WeightedBound c.e.source s (m + L) C A → WeightedBound c.e.source s (m + L) C B →
      WeightedBound c.e.source s (m + L) D (A - B) →
      WeightedBound Set.univ s m ((τ / s + ε / τ ^ tensorLoss P) * β) (d.mean hρ δ q A) ∧
      WeightedBound Set.univ s m (κ * (τ / s + ε / τ ^ tensorLoss P) * D)
        (d.mean hρ δ q A - d.mean hρ δ q B) := by
  let j := m + tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)
  let I := 2 ^ j * p.forms j * (j.factorial : ℝ) * p.inv j ^ j
  have hI : 0 ≤ I := by
    have := p.oneLEForms j
    have := p.oneLEInv j
    dsimp [I]
    positivity
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  have hA0 : 0 ≤ A₀ := zero_le_one.trans hA₀
  obtain ⟨E,hE,he⟩ := uniform_charted_combined_mean p.openU p.openO p.compact p.subsetDomain
    P p.smoothP p.C p.D p.J p.nonnegC p.oneLEJ q m (p.B m) (p.F m) A₀ (p.normal j)
    (p.oneLEB m) (p.nonnegF m) hA0 (zero_le_one.trans (p.oneLENormal j))
  refine ⟨max 1 E,max 1 (2 * E * I),le_max_left _ _,le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hε1 hsmall δ hδ A B D hC hD hA hB
    hballA hballB hbA hbB hbD
  have hj : m + (tensorOrder P + 1 + (q + 1) * (tensorOrder P + 1)) = j := by dsimp [j]; omega
  rw [hj] at hbA hbB hbD
  have hi : d.budgets.inv j = p.inv j := congrFun hd.inverse j
  have hq : d.budgets.forms j = p.forms j := congrFun hd.forms j
  have hp : d.budgets.psi j = p.psi j := congrFun hd.cutoff j
  obtain ⟨hu,hv,hbd⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target hi hq hp hs hs1
    A B D hC hD hA hB hballA hballB hbA hbB hbD
  have hmaps : Set.MapsTo (lowJet G) p.U p.Q := by
    simpa only [hd.domain, hd.range] using d.mapsJets
  have hgb : WeightedBound p.U s (m + tensorOrder P) (p.B m) (lowJet G) := by
    simpa only [hd.domain, hd.jets] using d.jetsBound m
  have hfb : ∀ v, WeightedBound p.U s (m + tensorOrder P) (p.F m)
      (fun x => fderiv ℝ φ x (coordinateVector v)) := by
    intro v
    simpa only [hd.domain, hd.phase] using d.phaseBound m v
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hdiff : supportedWeightedSeminorm c.chartCompact s j
      (d.amplitude hρ A - d.amplitude hρ B) ≤ A₀ * (I * D) := by
    simpa only [ChartedMeanData.amplitude, I, mul_assoc] using hbd
  have hh := he G hG φ K ε τ s c hd.domain hd.coefficients hd.perturbation hd.coordinates
    hτ hs hτs hs1 hε hε1 hsmall hmaps hgb hfb hn δ hδ (d.amplitude hρ A) (d.amplitude hρ B)
    (I * D) (mul_nonneg hI hD) hu hv hdiff
  have hη : 0 ≤ τ / s + ε / τ ^ tensorLoss P :=
    add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  constructor
  · exact hh.1.mono_const (mul_le_mul_of_nonneg_left (le_max_right _ _) hη)
  · apply hh.2.mono_const
    calc
      _ = (2 * E * I) * (τ / s + ε / τ ^ tensorLoss P) * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hη) hD

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
