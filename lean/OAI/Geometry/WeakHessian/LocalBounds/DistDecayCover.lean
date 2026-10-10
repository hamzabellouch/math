import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma exp_geometric_bound_eq (M C a : ℝ) (n : ℕ) :
    Real.exp (-a*(n:ℝ))*(M*Real.exp (C*((n:ℝ)+1))) =
      M*Real.exp C*(Real.exp (C-a))^n := by
  calc
    _ = M*(Real.exp (-a*(n:ℝ))*Real.exp (C*((n:ℝ)+1))) := by ring
    _ = M*Real.exp (-a*(n:ℝ)+C*((n:ℝ)+1)) := by rw [Real.exp_add]
    _ = M*Real.exp (C+(n:ℝ)*(C-a)) := by congr 2; ring
    _ = M*Real.exp C*Real.exp ((n:ℝ)*(C-a)) := by rw [Real.exp_add]; ring
    _ = _ := by rw [Real.exp_nat_mul]

noncomputable def distDecayCover (o : X) (a : ℝ) (n : ℕ) : X → ℝ≥0∞ :=
  (Metric.ball o ((n:ℝ)+1)).indicator (fun _ => ENNReal.ofReal (Real.exp (-a*(n:ℝ))))

lemma measurable_distDecayCover (o : X) (a : ℝ) (n : ℕ) : Measurable (distDecayCover o a n) :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
lemma exp_neg_dist_le_cover (o : X) {a : ℝ} (ha : 0 ≤ a) (x : X) :
    ENNReal.ofReal (Real.exp (-a*dist x o)) ≤ ∑' n, distDecayCover o a n x := by
  let n := ⌊dist x o⌋₊
  have hn : (n:ℝ) ≤ dist x o := Nat.floor_le dist_nonneg
  have hx : x ∈ Metric.ball o ((n:ℝ)+1) :=
    Metric.mem_ball.mpr (Nat.lt_floor_add_one (dist x o))
  calc
    _ ≤ distDecayCover o a n x := by
      simp only [distDecayCover,Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    _ ≤ _ := ENNReal.le_tsum (f := fun index => distDecayCover o a index x) n

lemma lintegral_distDecayCover_le (o : X) {M C a : ℝ}
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) (n : ℕ) :
    (∫⁻ x, distDecayCover o a n x ∂m) ≤ ENNReal.ofReal (M*Real.exp C*(Real.exp (C-a))^n) := by
  have H := hvol (n+1)
  simp only [Nat.cast_add,Nat.cast_one] at H
  calc
    _ = ENNReal.ofReal (Real.exp (-a*(n:ℝ)))*m (Metric.ball o ((n:ℝ)+1)) := by
      simp only [distDecayCover,lintegral_indicator Metric.isOpen_ball.measurableSet,lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (Real.exp (-a*(n:ℝ)))*ENNReal.ofReal (M*Real.exp (C*((n:ℝ)+1))) :=
      mul_le_mul_right H _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,exp_geometric_bound_eq]

lemma integrable_exp_neg_dist_of_growth (o : X) {M C a : ℝ} (_hM : 0 ≤ M)
    (ha : 0 ≤ a) (hCa : C < a)
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) :
    Integrable (fun x => Real.exp (-a*dist x o)) m := by
  have hs : Summable (fun n : ℕ => M*Real.exp C*(Real.exp (C-a))^n) :=
    (summable_geometric_of_norm_lt_one (show ‖Real.exp (C-a)‖ < 1 by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_lt_one_iff]; linarith)).mul_left (M*Real.exp C)
  refine ⟨(Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖Real.exp (-a*dist x o)‖ₑ ∂m) < ∞
  simp only [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  calc
    _ ≤ ∫⁻ x, ∑' n, distDecayCover o a n x ∂m := lintegral_mono (exp_neg_dist_le_cover o ha)
    _ = ∑' n, ∫⁻ x, distDecayCover o a n x ∂m :=
      lintegral_tsum (fun n => (measurable_distDecayCover o a n).aemeasurable)
    _ ≤ ∑' n, ENNReal.ofReal (M*Real.exp C*(Real.exp (C-a))^n) :=
      ENNReal.tsum_le_tsum (lintegral_distDecayCover_le o hvol)
    _ < ∞ := hs.tsum_ofReal_lt_top

lemma memLp_exp_neg_dist_of_growth (o : X) {M C a : ℝ} (hM : 0 ≤ M)
    (ha : 0 ≤ a) (hCa : C < 2*a)
    (hvol : ∀ n : ℕ, m (Metric.ball o (n:ℝ)) ≤ ENNReal.ofReal (M*Real.exp (C*(n:ℝ)))) :
    MemLp (fun x => Real.exp (-a*dist x o)) 2 m := by
  have hi := integrable_exp_neg_dist_of_growth o hM (by positivity : 0 ≤ 2*a) hCa hvol
  apply (memLp_two_iff_integrable_sq
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.dist continuous_const))).aestronglyMeasurable).mpr
  convert hi using 1
  ext x
  change (Real.exp (-a*dist x o))^2 = Real.exp (-(2*a)*dist x o)
  rw [← Real.exp_nat_mul]
  congr 1; ring

end WeakHessian

end
end InlinedFile0

end OAI
