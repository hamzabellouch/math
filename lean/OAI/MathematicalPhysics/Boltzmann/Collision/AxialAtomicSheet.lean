import OAI.MathematicalPhysics.Boltzmann.Collision.AxialFlow
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals

namespace OAI

section

/-!
# Uniform axial nonconcentration

The small-interval estimate and the vanishing velocity tails give one
modulus for every elementary sheet and every outgoing velocity off the axis.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.SheetTightness
open BoltzmannNonuniqueness.SheetIntervals

namespace BoltzmannNonuniqueness.AxialModulus

def axialRegion (v : Velocity) (a b : ℝ) : Set Coordinates :=
  {y | axial (PlaneChart.chart v y.1 y.2.1 y.2.2) ∈ Ioc a b}

def intervalMajorant (q L R ell : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * intervalBound q R ell

theorem tendsto_intervalMajorant {q : ℝ} (hq : q < 2) (L R : ℝ) :
    Tendsto (intervalMajorant q L R) (nhds 0) (nhds 0) := by
  have hc : ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top).ne
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L))
    (intervalBound_tendsto_zero hq R) (Or.inr hc)
  change Tendsto (fun ell => ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) *
    intervalBound q R ell) (nhds 0) (nhds 0)
  simpa only [mul_zero] using h

theorem axialRegion_subset (v : Velocity) (N : ℕ) (a b : ℝ) :
    axialRegion v a b ⊆ tailRegion v N ∪
      intervalRegion v (2 * ((N : ℝ) + 1)) a b := by
  intro y hy
  by_cases hr : 2 * ((N : ℝ) + 1) < radius v y
  · exact Or.inl hr
  · apply Or.inr
    apply (mem_intervalRegion _ _ _ _ _).mpr
    refine ⟨?_, hy⟩
    exact (le_add_of_nonneg_left (norm_nonneg y.1)).trans (le_of_not_gt hr)

theorem axialRegion_bound {q d L a b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hab : a < b)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) (N : ℕ) :
    normalizedMeasure (sheetLaw d ρ) q v (axialRegion v a b) ≤
      tailBound q L N + intervalMajorant q L (2 * ((N : ℝ) + 1)) (b - a) := by
  apply (measure_mono (axialRegion_subset v N a b)).trans
  apply (measure_union_le _ _).trans
  exact add_le_add (normalized_tail_bound hq₁ hq₂ hd hdmax hv hρ N)
    (normalized_interval_bound hq₁ hq₂ hd hdmax (by positivity) hab hv hρ)

/-- Uniform non-atomicity of the incoming axial marginal, with the full weight. -/
theorem uniform_axial_modulus {q L ε : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a b : ℝ), 0 < b - a → b - a ≤ δ →
      ∀ (d : ℝ) (ρ : Measure ℝ) (_ : IsProbabilityMeasure ρ)
        (_ : 0 ≤ d) (_ : d ≤ 1 / 8) (_ : AxialMoment ρ L)
        (v : Velocity) (_ : transverse v ≠ 0),
        normalizedMeasure (sheetLaw d ρ) q v (axialRegion v a b) ≤ ENNReal.ofReal ε := by
  have he : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have ht : ∀ᶠ n in atTop, tailBound q L n < ENNReal.ofReal (ε / 2) :=
    (tendsto_tailBound q L).eventually (gt_mem_nhds he)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  have hi : ∀ᶠ ell in nhds (0 : ℝ),
      intervalMajorant q L (2 * ((N : ℝ) + 1)) ell < ENNReal.ofReal (ε / 2) :=
    (tendsto_intervalMajorant hq₂ L _).eventually (gt_mem_nhds he)
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp hi
  refine ⟨r / 2, by linarith, ?_⟩
  intro a b hab hlen d ρ hprob hd hdmax hρ v hv
  have hdist : dist (b - a) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hab]
    linarith
  apply (axialRegion_bound hq₁ hq₂ hd hdmax (by linarith) hv hρ N).trans
  calc
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hN N le_rfl).le (hsmall hdist).le
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end BoltzmannNonuniqueness.AxialModulus

end

end

section

/-! # The limiting axial atoms belong to the proved zero-width sheet class -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AxialAtomicSheet

theorem sheetLaw_zero_dirac (u : ℝ) :
    SheetMeasures.sheetLaw 0 (Measure.dirac u) = Measure.dirac (PlaneChart.join 0 u) := by
  simp only [SheetMeasures.sheetLaw,SheetMeasures.transverseLaw,ite_true,
    Measure.dirac_prod_dirac]
  rw [Measure.map_dirac' SheetMeasures.join.measurable]
  rfl

theorem dirac_elementary {u R : ℝ} (hu : |u| ≤ R) :
    SheetClass.IsElementary (Real.exp (8*R^2)) (Measure.dirac (PlaneChart.join 0 u)) := by
  refine ⟨0,Measure.dirac u,le_rfl,by norm_num,inferInstance,?_,
    (sheetLaw_zero_dirac u).symm⟩
  constructor
  · exact integrable_dirac (by finiteness)
  · rw [integral_dirac]
    apply Real.exp_le_exp.mpr
    have hs : u^2 ≤ R^2 := by
      calc
        u^2 = |u|^2 := (sq_abs u).symm
        _ ≤ R^2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
    exact mul_le_mul_of_nonneg_left hs (by norm_num)

theorem velocity_abs_le {σ α γ μ t z : ℝ} (hα : 0 ≤ α) :
    |AxialFlow.velocity σ α γ μ t z| ≤ |σ|+α := by
  have h := AxialFlow.velocity_sub_center_le (σ := σ) (γ := γ) (s := μ) (t := t) (z := z) hα
  calc
    _ = |(AxialFlow.velocity σ α γ μ t z-σ)+σ| := by congr 1; ring
    _ ≤ |AxialFlow.velocity σ α γ μ t z-σ|+|σ| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem velocity_elementary {σ α γ μ t z : ℝ} (hα : 0 ≤ α) (hσ : |σ| = 1) :
    SheetClass.IsElementary (Real.exp (8*(1+α)^2))
      (Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) := by
  apply dirac_elementary
  simpa only [hσ] using velocity_abs_le (σ := σ) (γ := γ) (μ := μ) (t := t) (z := z) hα

theorem normalized_gain_bound {q σ α γ μ t z : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hα : 0 ≤ α) (hσ : |σ| = 1)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) q v ≤
        SheetTotal.bound q (Real.exp (8*(1+α)^2)) :=
  SheetClass.elementary_bound hq₁ hq₂ (velocity_elementary hα hσ) hv

end BoltzmannNonuniqueness.AxialAtomicSheet

end

end

end OAI
