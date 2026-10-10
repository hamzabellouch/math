import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel

namespace OAI

/-!
# Compact coefficient prediction families

The coefficient domain retains every earlier candidate label, including discarded
ones. A parent group has total mass at most one; the remaining mass is assigned
to the common terminal point. Weak limits are taken after evaluation. The
coefficient estimate passes through weakly closed norm balls and yields norm
continuity of the limit family.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology NNReal

namespace ReflexiveFixedPoints.Prediction

variable {I P X J : Type*} [Fintype I] [Fintype P] [DecidableEq P]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The coefficient of a candidate within one parent group. -/
def groupedCoefficient (parent : I → P) (theta : I → ℝ) (p : P) (i : I) : ℝ :=
  if parent i = p then theta i else 0

/-- Total coefficient mass belonging to one parent. -/
def coefficientSum (parent : I → P) (theta : I → ℝ) (p : P) : ℝ :=
  ∑ i, groupedCoefficient parent theta p i

/-- All nonnegative earlier-candidate coefficients with parent-group mass at most one. -/
def coefficientSet (parent : I → P) : Set (I → ℝ) :=
  {theta | (∀ i, 0 ≤ theta i) ∧ ∀ p, coefficientSum parent theta p ≤ 1}

@[simp] theorem groupedCoefficient_self {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P]
    (parent : I → P) (theta : I → ℝ) (i : I) :
    groupedCoefficient parent theta (parent i) i = theta i := by
  simp [groupedCoefficient]

theorem groupedCoefficient_nonneg {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P] (parent : I → P) {theta : I → ℝ}
    (htheta : ∀ i, 0 ≤ theta i) (p : P) (i : I) :
    0 ≤ groupedCoefficient parent theta p i := by
  unfold groupedCoefficient
  split_ifs <;> simp_all

theorem coefficientSum_nonneg (parent : I → P) {theta : I → ℝ}
    (htheta : ∀ i, 0 ≤ theta i) (p : P) :
    0 ≤ coefficientSum parent theta p :=
  Finset.sum_nonneg fun i _ => groupedCoefficient_nonneg parent htheta p i

theorem coefficient_le_one (parent : I → P) {theta : I → ℝ}
    (htheta : theta ∈ coefficientSet parent) (i : I) : theta i ≤ 1 := by
  have hi : groupedCoefficient parent theta (parent i) i ≤
      coefficientSum parent theta (parent i) :=
    Finset.single_le_sum
      (fun j _ => groupedCoefficient_nonneg parent htheta.1 (parent i) j)
      (Finset.mem_univ i)
  simpa only [groupedCoefficient_self] using hi.trans (htheta.2 (parent i))

@[simp] theorem zero_mem_coefficientSet {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P] (parent : I → P) :
    (0 : I → ℝ) ∈ coefficientSet parent := by
  simp [coefficientSet, coefficientSum, groupedCoefficient]

theorem coefficientSet_nonempty (parent : I → P) :
    (coefficientSet parent).Nonempty :=
  ⟨0, zero_mem_coefficientSet parent⟩

theorem continuous_coefficientSum {I P : Type*}
    [Fintype I] [Fintype P] [DecidableEq P] (parent : I → P) (p : P) :
    Continuous (fun theta : I → ℝ => coefficientSum parent theta p) := by
  unfold coefficientSum
  apply continuous_finsetSum
  intro i _
  by_cases hi : parent i = p
  · simpa only [groupedCoefficient, hi, ite_true] using continuous_apply (i : I)
  · simpa only [groupedCoefficient, hi, ite_false] using
      (continuous_const : Continuous (fun _ : I → ℝ => (0 : ℝ)))

theorem isClosed_coefficientSet (parent : I → P) :
    IsClosed (coefficientSet parent) := by
  unfold coefficientSet
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_iInter fun p => isClosed_le (continuous_coefficientSum parent p) continuous_const)

/-- Compactness uses a closed subset of the finite coefficient box, including the empty box. -/
theorem isCompact_coefficientSet (parent : I → P) :
    IsCompact (coefficientSet parent) := by
  have hbox : IsCompact {theta : I → ℝ | ∀ i, theta i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset (isClosed_coefficientSet parent)
  intro theta htheta i
  exact ⟨htheta.1 i, coefficient_le_one parent htheta i⟩

/-- The parent input predicted from earlier candidates and one common terminal point. -/
def residualPoint (parent : I → P) (y : I → X) (b : X) (theta : I → ℝ) (p : P) : X :=
  b + ∑ i, groupedCoefficient parent theta p i • (y i - b)

/-- The residual point is an actual finite convex combination. -/
theorem residualPoint_eq {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (parent : I → P) (y : I → X) (b : X)
    (theta : I → ℝ) (p : P) :
    residualPoint parent y b theta p =
      (1 - coefficientSum parent theta p) • b +
        ∑ i, groupedCoefficient parent theta p i • y i := by
  simp only [residualPoint, coefficientSum, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, sub_smul, one_smul]
  abel

/-- Nonnegative coefficients of mass at most one can be completed using the base point. -/
theorem residualPoint_mem (parent : I → P) {K : Set X} (hK : Convex ℝ K)
    (y : I → X) (hy : ∀ i, y i ∈ K) (b : X) (hb : b ∈ K)
    {theta : I → ℝ} (htheta : theta ∈ coefficientSet parent) (p : P) :
    residualPoint parent y b theta p ∈ K := by
  classical
  let w : Option I → ℝ := fun o =>
    match o with
    | none => 1 - coefficientSum parent theta p
    | some i => groupedCoefficient parent theta p i
  let z : Option I → X := fun o =>
    match o with
    | none => b
    | some i => y i
  have hw : ∀ o ∈ (Finset.univ : Finset (Option I)), 0 ≤ w o := by
    intro o _
    cases o with
    | none => exact sub_nonneg.mpr (htheta.2 p)
    | some i => exact groupedCoefficient_nonneg parent htheta.1 p i
  have hsum : ∑ o : Option I, w o = 1 := by
    simp [w, Fintype.sum_option, coefficientSum]
  have hz : ∀ o ∈ (Finset.univ : Finset (Option I)), z o ∈ K := by
    intro o _
    cases o with
    | none => exact hb
    | some i => exact hy i
  have hmem := hK.sum_mem hw hsum hz
  rw [residualPoint_eq]
  simpa [w, z, Fintype.sum_option] using hmem

/-- Subtracting predictions at two coefficient values cancels the base point exactly. -/
theorem residualPoint_sub {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (parent : I → P) (y : I → X) (b : X)
    (theta eta : I → ℝ) (p : P) :
    residualPoint parent y b theta p - residualPoint parent y b eta p =
      ∑ i, (groupedCoefficient parent theta p i -
        groupedCoefficient parent eta p i) • (y i - b) := by
  simp only [residualPoint, sub_smul, Finset.sum_sub_distrib]
  abel

/-- Uniform sum-norm coefficient bound for one parent input. -/
theorem residualPoint_norm_sub_le (parent : I → P) {K : Set X}
    (hdiam : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ 1)
    (y : I → X) (hy : ∀ i, y i ∈ K) (b : X) (hb : b ∈ K)
    (theta eta : I → ℝ) (p : P) :
    ‖residualPoint parent y b theta p - residualPoint parent y b eta p‖ ≤
      ∑ i, |theta i - eta i| := by
  rw [residualPoint_sub]
  calc
    ‖∑ i, (groupedCoefficient parent theta p i -
        groupedCoefficient parent eta p i) • (y i - b)‖
        ≤ ∑ i, ‖(groupedCoefficient parent theta p i -
          groupedCoefficient parent eta p i) • (y i - b)‖ := norm_sum_le _ _
    _ ≤ ∑ i, |theta i - eta i| := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : parent i = p
      · simp only [groupedCoefficient, hi, ite_true, norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hdiam (y i) (hy i) b hb)
      · simp [groupedCoefficient, hi, abs_nonneg]

/-- The closed norm ball, viewed in the weak topology, is closed. -/
theorem weaklyClosed_closedBallImage (r : ℝ) :
    IsClosed ((toWeakSpace ℝ X) '' Metric.closedBall (0 : X) r) := by
  have heq := (convex_closedBall (0 : X) r).toWeakSpace_closure ℝ
  rw [Metric.isClosed_closedBall.closure_eq] at heq
  rw [heq]
  exact isClosed_closure

/-- A uniform difference bound survives two weak limits along the same proper filter. -/
theorem norm_sub_le_of_weak_tendsto {F : Filter J} [F.NeBot]
    {a b : J → X} {za zb : X} {r : ℝ}
    (ha : Tendsto (fun j => toWeakSpace ℝ X (a j)) F (𝓝 (toWeakSpace ℝ X za)))
    (hb : Tendsto (fun j => toWeakSpace ℝ X (b j)) F (𝓝 (toWeakSpace ℝ X zb)))
    (hbound : ∀ j, ‖a j - b j‖ ≤ r) :
    ‖za - zb‖ ≤ r := by
  have hsub : Tendsto (fun j => toWeakSpace ℝ X (a j - b j)) F
      (𝓝 (toWeakSpace ℝ X (za - zb))) := by
    simpa only [map_sub] using ha.sub hb
  have hmem : toWeakSpace ℝ X (za - zb) ∈
      (toWeakSpace ℝ X) '' Metric.closedBall (0 : X) r :=
    (weaklyClosed_closedBallImage (X := X) r).mem_of_tendsto hsub
      (Filter.Eventually.of_forall fun j =>
        ⟨a j - b j, by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound j,
          rfl⟩)
  obtain ⟨z, hz, heq⟩ := hmem
  have hz' : z = za - zb := (toWeakSpace ℝ X).injective heq
  rw [hz'] at hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- In the default finite Pi metric, a sum-norm coefficient bound has constant `card I`. -/
theorem lipschitz_of_coefficient_bound {I X : Type*}
    [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : Set (I → ℝ)} (f : S → X)
    (hf : ∀ theta eta, ‖f theta - f eta‖ ≤ ∑ i, |theta.val i - eta.val i|) :
    LipschitzWith (Fintype.card I : ℝ≥0) f := by
  apply LipschitzWith.of_dist_le_mul
  intro theta eta
  calc
    dist (f theta) (f eta) = ‖f theta - f eta‖ := dist_eq_norm _ _
    _ ≤ ∑ i, |theta.val i - eta.val i| := hf theta eta
    _ ≤ ∑ _i : I, dist theta eta := by
      apply Finset.sum_le_sum
      intro i _
      rw [Subtype.dist_eq theta eta]
      simpa only [Real.dist_eq] using dist_le_pi_dist theta.val eta.val i
    _ = (Fintype.card I : ℝ≥0) * dist theta eta := by simp

/-- Continuity here has the norm topology on the target. -/
theorem continuous_of_coefficient_bound {S : Set (I → ℝ)} (f : S → X)
    (hf : ∀ theta eta, ‖f theta - f eta‖ ≤ ∑ i, |theta.val i - eta.val i|) :
    Continuous f :=
  (lipschitz_of_coefficient_bound f hf).continuous

/-- Weak convergence after evaluation preserves the coefficient bound. -/
theorem weakLimit_coefficient_bound {S : Set (I → ℝ)} {F : Filter J} [F.NeBot]
    (q : J → S → X) (z : S → X)
    (hz : ∀ theta, Tendsto (fun j => toWeakSpace ℝ X (q j theta)) F
      (𝓝 (toWeakSpace ℝ X (z theta))))
    (hq : ∀ j theta eta, ‖q j theta - q j eta‖ ≤ ∑ i, |theta.val i - eta.val i|)
    (theta eta : S) :
    ‖z theta - z eta‖ ≤ ∑ i, |theta.val i - eta.val i| :=
  norm_sub_le_of_weak_tendsto (hz theta) (hz eta) (fun j => hq j theta eta)

/-- Uniform coefficient bounds give norm continuity of the already evaluated weak limits. -/
theorem continuous_weakLimit_of_coefficient_bound {S : Set (I → ℝ)}
    {F : Filter J} [F.NeBot] (q : J → S → X) (z : S → X)
    (hz : ∀ theta, Tendsto (fun j => toWeakSpace ℝ X (q j theta)) F
      (𝓝 (toWeakSpace ℝ X (z theta))))
    (hq : ∀ j theta eta, ‖q j theta - q j eta‖ ≤ ∑ i, |theta.val i - eta.val i|) :
    Continuous z :=
  continuous_of_coefficient_bound z (weakLimit_coefficient_bound q z hz hq)

/-- Compactness of the coefficient space yields norm compactness of the weak-limit image. -/
theorem isCompact_weakLimit_image (parent : I → P) {F : Filter J} [F.NeBot]
    (q : J → coefficientSet parent → X) (z : coefficientSet parent → X)
    (hz : ∀ theta, Tendsto (fun j => toWeakSpace ℝ X (q j theta)) F
      (𝓝 (toWeakSpace ℝ X (z theta))))
    (hq : ∀ j theta eta, ‖q j theta - q j eta‖ ≤ ∑ i, |theta.val i - eta.val i|) :
    IsCompact (Set.range z) := by
  let : CompactSpace (coefficientSet parent) :=
    isCompact_iff_compactSpace.mp (isCompact_coefficientSet parent)
  exact isCompact_range (continuous_weakLimit_of_coefficient_bound q z hz hq)

end ReflexiveFixedPoints.Prediction

end

end OAI
