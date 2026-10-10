import OAI.Analysis.CircleDomains.Modulus.AdmissiblePathCost
import OAI.Analysis.CircleDomains.Probability.CountableVisitNorm
import OAI.Analysis.CircleDomains.Selection.CodeBarycenterDensities

namespace OAI

/-! Positive perturbations of the physical density and atomic tolls.
Their norm increase is controlled by the finite physical area and the
chosen square-summable countable weights. -/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

def squareIntegralNorm {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ := (∫⁻ y, f y ^ 2 ∂μ) ^ (1 / 2 : ℝ)

theorem squareIntegralNorm_add_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {f g : Y → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    squareIntegralNorm μ (f + g) ≤ squareIntegralNorm μ f + squareIntegralNorm μ g := by
  simpa only [squareIntegralNorm, ENNReal.rpow_two] using
    ENNReal.lintegral_Lp_add_le (μ := μ) (p := (2 : ℝ)) hf.aemeasurable hg.aemeasurable
      (by norm_num)

theorem squareIntegralNorm_const {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (δ : ℝ≥0∞) :
    squareIntegralNorm μ (fun _ => δ) = δ * (μ univ) ^ (1 / 2 : ℝ) := by
  rw [squareIntegralNorm, lintegral_const,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have he : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [he]

theorem countingSquareNorm_mul {D : Type*} (δ : ℝ≥0∞) (c : D → ℝ≥0∞) :
    countingSquareNorm (fun s => δ * c s) = δ * countingSquareNorm c := by
  simp only [countingSquareNorm, mul_pow]
  rw [ENNReal.tsum_mul_left, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have he : (δ ^ 2) ^ (1 / 2 : ℝ) = δ := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  rw [he]

variable {Y D : Type*} [MetricSpace Y] [TopologicalSpace D]
  [MeasurableSpace Y] [BorelSpace Y] [MeasurableSpace D] [BorelSpace D]

def perturbedPhysicalDensity (h : PathCostSpace Y D → ℝ≥0∞) (δ : ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  h (costPhysical y) + δ

def perturbedAtomicToll (h : PathCostSpace Y D → ℝ≥0∞) (c : D → ℝ≥0∞)
    (δ : ℝ≥0∞) (s : D) : ℝ≥0∞ := c s * h (costAtomic s) + δ * c s

theorem perturbedPhysicalDensity_norm (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    (δ : ℝ≥0∞) :
    squareIntegralNorm μ (perturbedPhysicalDensity h δ) ≤
      squareIntegralNorm (pathCostReference μ c τ) h + δ * (μ univ) ^ (1 / 2 : ℝ) := by
  have hs := squareIntegralNorm_add_le μ (hh.comp measurable_costPhysical)
    (measurable_const (a := δ))
  rw [squareIntegralNorm_const] at hs
  apply hs.trans
  apply add_le_add _ le_rfl
  exact ENNReal.rpow_le_rpow (codeReference_component_energies μ c τ h hh).1 (by norm_num)

variable [Countable D]

theorem perturbedAtomicToll_norm (μ : Measure Y) (c : D → ℝ≥0∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    (δ : ℝ≥0∞) :
    countingSquareNorm (perturbedAtomicToll h c δ) ≤
      squareIntegralNorm (pathCostReference μ c τ) h + δ * countingSquareNorm c := by
  have hs := countingSquareNorm_add_le (fun s => c s * h (costAtomic s)) (fun s => δ * c s)
  rw [countingSquareNorm_mul] at hs
  apply hs.trans
  apply add_le_add _ le_rfl
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  rw [squareIntegral_pathCostReference μ c τ h hh]
  exact le_trans le_add_self le_self_add

theorem exists_small_positive_perturbation (μ : Measure Y) [IsFiniteMeasure μ]
    (c : D → ℝ≥0∞) (hc : (∑' s, c s ^ 2) < ∞)
    (τ : Measure LevelTuple) {h : PathCostSpace Y D → ℝ≥0∞} (hh : Measurable h)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      squareIntegralNorm μ (perturbedPhysicalDensity h δ) +
        countingSquareNorm (perturbedAtomicToll h c δ) ≤
      2 * squareIntegralNorm (pathCostReference μ c τ) h + ε := by
  let K : ℝ≥0∞ := (μ univ) ^ (1 / 2 : ℝ) + countingSquareNorm c
  have hK : K ≠ ∞ := ENNReal.add_ne_top.mpr
    ⟨ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ),
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc.ne⟩
  obtain ⟨δ, hδ, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hK hε.ne'
  refine ⟨δ, hδ, ?_⟩
  have he := add_le_add (perturbedPhysicalDensity_norm μ c τ hh (δ : ℝ≥0∞))
    (perturbedAtomicToll_norm μ c τ hh (δ : ℝ≥0∞))
  calc
    _ ≤ (squareIntegralNorm (pathCostReference μ c τ) h + δ * (μ univ) ^ (1 / 2 : ℝ)) +
        (squareIntegralNorm (pathCostReference μ c τ) h + δ * countingSquareNorm c) := he
    _ = 2 * squareIntegralNorm (pathCostReference μ c τ) h + δ * K := by
      dsimp [K]
      rw [mul_add, two_mul]
      ac_rfl
    _ ≤ _ := add_le_add le_rfl hsmall.le

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [Countable D] in
theorem perturbed_cost_ge_one (d : PathCodeData X Y) (p : D → X) (c : D → ℝ≥0∞)
    (ν : Measure X) (Γ : BasePathCode d) (h : PathCostSpace Y D → ℝ≥0∞) (hh : Measurable h)
    (hΓ : EndpointCode d ν (tupleInfiniteExclusions (h ∘ costTuple)) Γ.val)
    (hadm : CostAdmissible d p c ν h) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    1 ≤ physicalAtomicCost d p Γ (perturbedPhysicalDensity h δ) (perturbedAtomicToll h c δ) := by
  exact physicalAtomicCost_ge_one d p c ν Γ h hh hΓ hadm _ _ hδ
    (fun _ => le_self_add) (fun _ => le_self_add) (fun _ => le_add_self)

end CircleDomainRigidity

end

end OAI
