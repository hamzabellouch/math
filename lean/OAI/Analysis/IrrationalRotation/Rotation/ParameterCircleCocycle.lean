import OAI.Analysis.IrrationalRotation.Model.ParameterCircleWeights
import OAI.Analysis.IrrationalRotation.Rotation.CircleCocycle
import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseSummability

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterData

theorem coord_phase_eq (p : CircleParameterData) (θ : ℝ) (i : p.Coord) :
    CircleWeights.phase θ p.coordFrequency i = p.alpha θ i.2 := by
  simp only [CircleWeights.phase, coordFrequency, alpha, Int.cast_natCast]

theorem coord_coordinate_eq (p : CircleParameterData) (i : p.Coord) (x : Circle) :
    CircleWeights.coordinate p.coordFrequency i x = p.coordinate i.2 x := by
  simp only [CircleWeights.coordinate, CircleWeights.representative,
    coordFrequency, coordinate, rep, natCast_zsmul]

theorem floorCocycle_eq_block_sum (p : CircleParameterData) (θ : ℝ) (k : ℤ)
    (x : Circle) (hx : HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) :
    p.floorCocycle θ k x = Real.exp (-(∑' j : ℕ, p.C (j + 1) *
      ∑ i ∈ p.block (j + 1),
        (Int.floor (p.coordinate i x + (k : ℝ) * p.alpha θ i) : ℝ))) := by
  unfold floorCocycle CircleWeights.cocycle CircleWeights.floorCost
  simp_rw [p.coord_phase_eq, p.coord_coordinate_eq]
  congr 2
  rw [(FiniteSupportCocycle.summable_weighted_int p.coordCost hx).tsum_sigma]
  apply tsum_congr
  intro j
  simp only [coordCost, tsum_fintype]
  rw [Finset.mul_sum]
  exact Finset.sum_attach (p.block (j + 1))
    (fun i => p.C (j + 1) *
      (Int.floor (p.coordinate i x + (k : ℝ) * p.alpha θ i) : ℝ))

theorem floorCocycle_pos (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) :
    0 < p.floorCocycle θ k x := Real.exp_pos _

theorem floorCocycle_zero (p : CircleParameterData) (θ : ℝ) (x : Circle) :
    p.floorCocycle θ 0 x = 1 :=
  CircleWeights.cocycle_zero θ p.coordFrequency p.coordCost x

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordFrequency_ne_zero (i : p.Coord) : p.coordFrequency i ≠ 0 := by
  change (p.q i.2 : ℤ) ≠ 0
  exact_mod_cast (hp.q_pos i.2).ne'

theorem coordCost_pos (i : p.Coord) : 0 < p.coordCost i :=
  hp.C_pos (i.1 + 1) (by omega)

theorem summable_coord_phases : Summable (CircleWeights.phase θ p.coordFrequency) := by
  rw [show CircleWeights.phase θ p.coordFrequency =
    (fun i : p.Coord => p.alpha θ i.2) from funext (p.coord_phase_eq θ)]
  apply (summable_sigma_of_nonneg (fun i => Int.fract_nonneg _)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply hp.summable_block_phases.congr
    intro j
    simp only [tsum_fintype]
    exact (Finset.sum_attach (p.block (j + 1)) (p.alpha θ)).symm

theorem tsum_coord_log_cost_eq_top :
    (∑' i : p.Coord, ENNReal.ofReal (p.coordCost i) *
      ENNReal.ofReal (CircleWeights.phase θ p.coordFrequency i)) = ∞ := by
  calc
    (∑' i : p.Coord, ENNReal.ofReal (p.coordCost i) *
        ENNReal.ofReal (CircleWeights.phase θ p.coordFrequency i)) =
        ∑' j : ℕ, ENNReal.ofReal
          (p.C (j + 1) * ∑ i ∈ p.block (j + 1), p.alpha θ i) := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro j
      simp only [CircleParameterData.coordCost, p.coord_phase_eq, tsum_fintype]
      simp_rw [← ENNReal.ofReal_mul (hp.C_pos (j + 1) (by omega)).le]
      have hnn : ∀ i ∈ p.block (j + 1), 0 ≤ p.C (j + 1) * p.alpha θ i :=
        fun i _ => mul_nonneg (hp.C_pos (j + 1) (by omega)).le (Int.fract_nonneg _)
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg hnn]
      exact Finset.sum_attach (p.block (j + 1))
        (fun i => ENNReal.ofReal (p.C (j + 1) * p.alpha θ i))
    _ = ∞ := hp.tsum_block_log_cost_eq_top

theorem measurable_parameter_weight : Measurable (p.measurableWeight θ) := by
  exact CircleWeights.measurable_cocycle θ p.coordFrequency hp.coordFrequency_ne_zero
    p.coordCost 1

theorem measurable_parameter_cocycle (k : ℤ) : Measurable (p.floorCocycle θ k) :=
  CircleWeights.measurable_cocycle θ p.coordFrequency hp.coordFrequency_ne_zero
    p.coordCost k

theorem parameter_cocycle_antitone (x : Circle)
    (hx : ∀ k : ℤ, HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) :
    Antitone (fun k : ℤ => p.floorCocycle θ k x) := by
  apply CircleWeights.cocycle_antitone_of_finite_support θ p.coordFrequency p.coordCost
    (fun i => (hp.coordCost_pos i).le) x
  simpa only [p.coord_phase_eq, p.coord_coordinate_eq] using hx

theorem parameter_weight_mem_Ioc (x : Circle) :
    p.measurableWeight θ x ∈ Ioc (0 : ℝ) 1 :=
  CircleWeights.weight_mem_Ioc θ p.coordFrequency p.coordCost
    (fun i => (hp.coordCost_pos i).le) x

theorem exists_parameter_cocycle_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i : p.Coord =>
          Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        p.floorCocycle θ (k + n) x =
          p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x) := by
  simpa only [circleMeasure, CircleParameterData.floorCocycle,
    p.coord_phase_eq, p.coord_coordinate_eq] using
    CircleWeights.exists_cocycle_set θ p.coordFrequency hp.coordFrequency_ne_zero
      p.coordCost hp.summable_coord_phases

end CircleParameterLaws
end Invariant233

end OAI
