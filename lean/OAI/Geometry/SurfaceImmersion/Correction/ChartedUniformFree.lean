import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeResidual
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanProfile
import OAI.Geometry.SurfaceImmersion.Atlas.ChartedUniformAmplitude

namespace OAI

/-! Uniform size and full-linearization residuals for the actual free
oscillation used by the charted mean construction. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}

def displacement (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) : RField 4 :=
  c.freeDisplacement δ q (d.amplitude hρ A)

lemma displacement_smooth_support (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (δ : ℝ) (q : ℕ) (A : SmallModes.Base → Tensor) :
    ContDiff ℝ ∞ (d.displacement hρ δ q A) ∧
      tsupport (d.displacement hρ δ q A) ⊆ (modeSupport K : Set SmallModes.Base) :=
  c.freeDisplacement_smooth_support δ q (d.amplitude hρ A)

end ChartedMeanData

theorem uniform_charted_free_bounds {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (p : ChartedMeanProfile P) {ρ R : ℝ} (hρ : 0 < ρ) (q m : ℕ) (C : ℝ) :
    ∃ B E : ℝ, 1 ≤ B ∧ 1 ≤ E ∧ ∀ {G : Base → Space} {hG : ContDiff ℝ ∞ G}
      {φ : Base → ℝ} {K : Compacts Base} {ε τ : ℝ} {s : ℝ≥0}
      {c : PolynomialSolveData P ε G hG φ K τ s}
      {r : ℝ} {reference : SmallModes.Base → Tensor}
      (d : ChartedMeanData c r ρ R reference), p.Fits d →
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε →
      τ / s + ε / τ ^ tensorLoss P ≤ 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ A : SmallModes.Base → Tensor, 0 ≤ C → ContDiff ℝ ∞ A → InTrialBall Set.univ reference r A →
      WeightedBound Set.univ s (PolynomialSolveData.inputOrder (P := P) q m) C A →
      WeightedBound Set.univ τ m (B * (δ * τ)) (d.displacement hρ δ q A) ∧
      WeightedBound Set.univ τ m (E * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1))
        (coordinateFullLinearized P ε G (d.displacement hρ δ q A)) := by
  let j := PolynomialSolveData.inputOrder (P := P) q m
  obtain ⟨A₀,hA₀,ha⟩ := uniform_charted_trial_amplitude (R := R) p.openV hρ j C
    (p.inv j) (p.forms j) (p.psi j) (p.oneLEInv j) (p.oneLEForms j) (p.oneLEPsi j)
  let B₀ := (m.factorial : ℝ) * 2 ^ m * correctedSeedBudget (tensorOrder P) p.C p.D q m (p.normal j) *
    p.J m ^ m
  let κ := fun k => max (SmallModes.errorConstant k (p.C k))
    (p.D k * SmallModes.initialConstant 4 (k + tensorOrder P) (p.C (k + tensorOrder P)))
  let γ := fun k => max (SmallModes.fullErrorConstant 4 k (p.C k))
    (p.D k * SmallModes.initialConstant 4 (k + tensorOrder P) (p.C (k + tensorOrder P)))
  let E₀ := tensorChartBudget m (p.J m) (p.J (m + 1)) * 2 ^ m *
    (FiniteParametrix.boundProfile (tensorOrder P + 1) κ γ q m * (Real.sqrt 2 * 2 ^ j * p.normal j))
  refine ⟨max 1 (B₀ * A₀),max 1 (E₀ * A₀),le_max_left _ _,le_max_left _ _,?_⟩
  intro G hG φ K ε τ s c r reference d hd hτ hs hτs hs1 hε hsmall δ hδ A hC hA hball hbA
  have hi : d.budgets.inv j = p.inv j := congrFun hd.inverse j
  have hq : d.budgets.forms j = p.forms j := congrFun hd.forms j
  have hp : d.budgets.psi j = p.psi j := congrFun hd.cutoff j
  have hz : WeightedBound c.e.source s j 0 (A - A) := by
    apply (weightedBound_zero c.e.source s j (F := Tensor)).congr
    intro x _
    exact sub_self (A x)
  obtain ⟨hu,_,_⟩ := ha c d.cutoff d.form d.localBounds d.budgets hd.target hi hq hp hs hs1
    A A 0 hC le_rfl hA.contDiffOn hA.contDiffOn
    (fun x _ => hball x (Set.mem_univ x)) (fun x _ => hball x (Set.mem_univ x))
    (hbA.restrict_open c.e.open_source) (hbA.restrict_open c.e.open_source) hz
  have hn : WeightedBound c.e.target s j (p.normal j) (freeNormal c.realMap) := by
    simpa only [hd.normal] using d.budgets.normal_bound j
  have hsize := c.freeDisplacement_bound hδ hτ hs hτs hs1 hε hsmall q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have hres := c.freeDisplacement_residual_bound hδ hτ hs hτs hs1 hε q m
    (zero_le_one.trans hA₀) (zero_le_one.trans (p.oneLENormal j)) hn (d.amplitude hρ A) hu
  have heqB : c.freeSizeFactor q m (p.normal j) = B₀ := by
    simp only [PolynomialSolveData.freeSizeFactor,hd.coefficients,hd.perturbation,hd.coordinates,B₀]
  have heqE : c.freeResidualFactor q m (p.normal j) = E₀ := by
    have hk : c.κ = κ := by
      funext k
      simp only [PolynomialSolveData.κ,hd.coefficients,hd.perturbation,κ]
    have hg : c.freeInitialFactor = γ := by
      funext k
      simp only [PolynomialSolveData.freeInitialFactor,hd.coefficients,hd.perturbation,γ]
    simp only [PolynomialSolveData.freeResidualFactor,PolynomialSolveData.freeChartResidualFactor,
      hk,hg,hd.coordinates,E₀,j]
  rw [heqB] at hsize
  rw [heqE] at hres
  constructor
  · apply hsize.mono_const
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_right 1 (B₀ * A₀))
      (mul_nonneg hδ hτ.le)
  · apply hres.mono_const
    have hη : 0 ≤ (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) :=
      pow_nonneg (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _
    calc
      _ = (E₀ * A₀) * (δ * τ) * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg hδ hτ.le)) hη

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
