import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveCorrectionStep
import OAI.Geometry.SurfaceImmersion.Correction.AdaptiveOrderControl
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldCorrectionLimit

namespace OAI

/-! Construction of the correction sequence, and unbounded growth of the
finite derivative order despite the absence of uniform high-order input bounds. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates
local instance sequenceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance sequenceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance sequenceDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance sequenceDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance sequenceSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance sequenceSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection
variable (c : PreparedCorrection d) (hF : ContMDiff planeModel spaceModel ∞ F)
  {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)

def chosenTransition {n : ℕ} (s : c.Stage t n) : c.Transition s :=
  Classical.choice (c.transition_nonempty hF ht htsmall s)

def sequence (seed : c.Stage t 0) : (n : ℕ) → c.Stage t n
  | 0 => seed
  | n+1 => (c.chosenTransition hF ht htsmall (sequence seed n)).next

def increment (seed : c.Stage t 0) (n : ℕ) : M → Space :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).increment

lemma sequence_succ_map (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).map =
    (c.sequence hF ht htsmall seed n).map+c.increment hF ht htsmall seed n :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).map_eq

lemma sequence_succ_order (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).order =
      if (c.sequence hF ht htsmall seed n).CanAdvance then
        (c.sequence hF ht htsmall seed n).order+1 else
        (c.sequence hF ht htsmall seed n).order :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).order_eq

lemma sequence_order_monotone (seed : c.Stage t 0) :
    Monotone (fun n => (c.sequence hF ht htsmall seed n).order) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [c.sequence_succ_order hF ht htsmall seed n]
  split_ifs <;> omega

lemma increment_smooth (seed : c.Stage t 0) (n : ℕ) :
    ContMDiff planeModel spaceModel ∞ (c.increment hF ht htsmall seed n) :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).smooth

lemma sequence_partialMap (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed n).map =
    manifoldPartialMap seed.map (c.increment hF ht htsmall seed) n := by
  induction n with
  | zero => funext x; simp [sequence,manifoldPartialMap]
  | succ n ih =>
    rw [c.sequence_succ_map hF ht htsmall seed n,ih]
    funext x
    simp only [Pi.add_apply,manifoldPartialMap,Finset.sum_range_succ]
    abel

lemma sequence_size_recurrence (seed : c.Stage t 0) (m n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).size m ≤ c.baseline+
      c.N (c.sequence hF ht htsmall seed n).order m*(correctionScale t n)^(1/5 : ℝ)*
        (1+(c.sequence hF ht htsmall seed n).size m) := by
  let s := c.sequence hF ht htsmall seed n
  have hex := s.finiteInput ht htsmall m
  have hx : 0 ≤ s.size m := d.A.inputSize_nonneg hex
  have hbound := (c.chosenTransition hF ht htsmall s).recurrence m (s.size m)
    hx (d.A.inputSize_bound hex)
  exact d.A.inputSize_le (add_nonneg c.baseline_nonneg
    (mul_nonneg (mul_nonneg (c.N_nonneg s.order m)
      (Real.rpow_nonneg (correctionScale_pos ht n).le _)) (by linarith))) hbound

/-- The adaptive order really tends to infinity. The proof uses the actual
finite norm of every stage and the all-order affine recurrence. -/
theorem sequence_order_tendsto (seed : c.Stage t 0) :
    Tendsto (fun n => (c.sequence hF ht htsmall seed n).order) atTop atTop := by
  apply adaptive_order_tendsto (x := fun m n => (c.sequence hF ht htsmall seed n).size m)
    (t := correctionScale t) (N := c.N) (ε := c.ε) (r := correctionInputOrder)
    c.baseline_nonneg (lt_trans c.baseline_lt (by linarith [c.budget_pos])) c.budget_pos
    c.N_nonneg c.ε_pos (correctionScale_pos ht)
    (correctionScale_tendsto_zero ht.le htsmall)
  · intro m n
    exact d.A.inputSize_nonneg ((c.sequence hF ht htsmall seed n).finiteInput ht htsmall m)
  · exact c.sequence_size_recurrence hF ht htsmall seed
  · exact c.sequence_order_monotone hF ht htsmall seed
  · intro n hε hb
    have ha : (c.sequence hF ht htsmall seed n).CanAdvance := ⟨hε,hb⟩
    rw [c.sequence_succ_order hF ht htsmall seed n,ite_eq_left ha]

lemma increment_eventual_bound (seed : c.Stage t 0) (m : ℕ) :
    ∀ᶠ n in atTop, d.A.WeightedBound 1 m (c.ρ*correctionScale t n)
      (c.increment hF ht htsmall seed n) := by
  filter_upwards [(c.sequence_order_tendsto hF ht htsmall seed).eventually
    (eventually_ge_atTop (2*m))] with n hn
  exact (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).small m
    (by unfold correctionOrder; omega)

lemma sequence_amplitude_tendsto (seed : c.Stage t 0) :
    Tendsto (fun n => (correctionScale t n)^
      (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Real.rpow_nonneg (correctionScale_pos ht n).le _)
    (fun n => ?_) (correctionScale_tendsto_zero ht.le htsmall)
  have hsn := correctionScale_pos ht n
  have hs1 : correctionScale t n ≤ 1 :=
    (correctionScale_le_initial ht.le htsmall n).trans (by linarith)
  have hexp : (1 : ℝ) ≤ (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ) := by
    unfold correctionOrder
    exact_mod_cast (show 1 ≤ (c.sequence hF ht htsmall seed n).order+10 by omega)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hsn hs1 hexp

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
