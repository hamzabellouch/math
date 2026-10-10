import OAI.Combinatorics.GraphThreshold.Basic
import OAI.Combinatorics.GraphThreshold.FiniteProbability
import OAI.Combinatorics.GraphThreshold.ProbabilityTreeFacts
import OAI.Combinatorics.GraphThreshold.TreeReductionData
import OAI.Combinatorics.GraphThreshold.OutsideChangeOfMeasure
import OAI.Combinatorics.GraphThreshold.LocalFailure
import OAI.Combinatorics.GraphThreshold.CapacityIteration
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

/-!
# The bad-node potential for simultaneous tree reduction

All nodes in a reduction use the same random set. The expectation argument
uses an outside-coordinate change of measure, rather than independence of
node outcomes.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace LeanBlast.SecondKahnKalai

/-- One step of the actual recursive bad-node potential. -/
def nodePotential {B : Type*} [Fintype B] (m : ℕ) (failure : ℝ)
    (target childPotential : B → ℝ) : ℝ :=
  (failure + ∑ b, target b * childPotential b) / Real.exp (-(m : ℝ))

theorem nodePotential_nonneg {B : Type*} [Fintype B] (m : ℕ) (failure : ℝ)
    (target childPotential : B → ℝ) (hf : 0 ≤ failure)
    (ht : ∀ b, 0 ≤ target b) (hc : ∀ b, 0 ≤ childPotential b) :
    0 ≤ nodePotential m failure target childPotential := by
  exact div_nonneg (add_nonneg hf (Finset.sum_nonneg (fun b _ => mul_nonneg (ht b) (hc b))))
    (Real.exp_pos _).le

/-- A failed good-mass threshold forces the recursively defined potential
above one. Children with zero target mass require no special treatment. -/
theorem one_lt_nodePotential_of_bad {B : Type*} [Fintype B]
    (m : ℕ) (failure : ℝ) (target childPotential : B → ℝ) (good : B → Prop)
    (ht : ∀ b, 0 ≤ target b) (hc : ∀ b, 0 ≤ childPotential b)
    (hmass : failure + ∑ b, target b = 1)
    (hchild : ∀ b, ¬good b → 1 < childPotential b)
    (hbad : (∑ b, if good b then target b else 0) < 1 - Real.exp (-(m : ℝ))) :
    1 < nodePotential m failure target childPotential := by
  classical
  have hsplit : (∑ b, if good b then target b else 0) +
      (∑ b, if good b then 0 else target b) = ∑ b, target b := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : good b <;> simp [hb]
  have hsum : (∑ b, if good b then 0 else target b) ≤
      ∑ b, target b * childPotential b := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : good b
    · simpa only [ite_eq_left hb] using mul_nonneg (ht b) (hc b)
    · simpa only [ite_eq_right hb, mul_one] using
        mul_le_mul_of_nonneg_left (hchild b hb).le (ht b)
  unfold nodePotential
  apply (lt_div_iff₀ (Real.exp_pos _)).mpr
  nlinarith

theorem bernoulliExpectation_nodePotential {X B : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] (p : ℝ) (m : ℕ) (failure : Finset X → ℝ)
    (target childPotential : B → Finset X → ℝ) :
    bernoulliExpectation p (fun W => nodePotential m (failure W)
      (fun b => target b W) (fun b => childPotential b W)) =
      (bernoulliExpectation p failure +
        ∑ b, bernoulliExpectation p (fun W => target b W * childPotential b W)) /
        Real.exp (-(m : ℝ)) := by
  unfold bernoulliExpectation nodePotential
  dsimp only
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro W _
  rw [← mul_div_assoc, mul_add, Finset.mul_sum]

/-- The expectation recursion uses one change-of-measure estimate per child;
it does not factor a product of dependent random variables. -/
theorem bernoulliExpectation_nodePotential_le {X B : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] (p : ℝ) (m : ℕ) (ν : FiniteLaw B) (failure : Finset X → ℝ)
    (target childPotential : B → Finset X → ℝ)
    (hfailure : bernoulliExpectation p failure ≤ Real.exp (-9 * (m : ℝ)))
    (hchild : ∀ b,
      bernoulliExpectation p (fun W => target b W * childPotential b W) ≤
        Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p (childPotential b)) :
    bernoulliExpectation p (fun W => nodePotential m (failure W)
      (fun b => target b W) (fun b => childPotential b W)) ≤
      Real.exp (-8 * (m : ℝ)) + Real.exp (12 * (m : ℝ)) *
        ν.expectation (fun b => bernoulliExpectation p (childPotential b)) := by
  rw [bernoulliExpectation_nodePotential]
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hchild b)
  have hsum : (∑ b, Real.exp (11 * (m : ℝ)) * ν.weight b *
      bernoulliExpectation p (childPotential b)) =
      Real.exp (11 * (m : ℝ)) * ν.expectation
        (fun b => bernoulliExpectation p (childPotential b)) := by
    unfold FiniteLaw.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hbound := div_le_div_of_nonneg_right (add_le_add hfailure hs) (Real.exp_pos (-(m : ℝ))).le
  rw [hsum] at hbound
  refine hbound.trans_eq ?_
  have hfirst : Real.exp (-9 * (m : ℝ)) / Real.exp (-(m : ℝ)) =
      Real.exp (-8 * (m : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hsecond : Real.exp (11 * (m : ℝ)) / Real.exp (-(m : ℝ)) =
      Real.exp (12 * (m : ℝ)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [add_div, hfirst, mul_div_right_comm, hsecond]

/-- Deterministic envelope obtained by iterating the expectation recursion. -/
def potentialEnvelope : ℕ → (ℕ → ℕ) → ℝ
  | 0, _ => 0
  | d + 1, m => Real.exp (-8 * (m 0 : ℝ)) + Real.exp (12 * (m 0 : ℝ)) *
      potentialEnvelope d (fun j => m (j + 1))

theorem potentialEnvelope_eq_sum (d : ℕ) (m : ℕ → ℕ) :
    potentialEnvelope d m =
      ∑ j ∈ Finset.range d,
        Real.exp (12 * (∑ h ∈ Finset.range j, (m h : ℝ)) - 8 * (m j : ℝ)) := by
  induction d generalizing m with
  | zero => simp [potentialEnvelope]
  | succ d ih =>
    rw [potentialEnvelope, ih, Finset.sum_range_succ']
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_sub, neg_mul]
    rw [Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← Real.exp_add, Finset.sum_range_succ']
    congr 1
    ring

section Trees

variable {X : Type} [Fintype X] [DecidableEq X]

def treePotential (p : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) : ℝ :=
  match T with
  | .leaf => 0
  | @ProbabilityTree.node _ _ B inst ν hν A child =>
      nodePotential (m 0) (localFailureMass ν A p (m 0) W)
        (successfulTargetMass ν A p (m 0) W)
        (fun b => treePotential p (fun j => m (j + 1)) W (child b))
termination_by d

omit [Fintype X] in
theorem treePotential_nonneg {p : ℝ} (hp : 0 ≤ p) (m : ℕ → ℕ) (W : Finset X)
    {d : ℕ} (T : ProbabilityTree X d) : 0 ≤ treePotential p m W T := by
  induction T generalizing m with
  | leaf => simp only [treePotential, le_refl]
  | @node d B inst ν hν A child ih =>
      simp only [treePotential]
      exact nodePotential_nonneg (m 0) _ _ _ (localFailureMass_nonneg ν A hp (m 0) W)
        (fun b => successfulTargetMass_nonneg ν A hp (m 0) W b)
        (fun b => ih b (fun j => m (j + 1)))

omit [Fintype X] in
theorem one_lt_treePotential_of_not_good {p : ℝ} (hp : 0 < p) (m : ℕ → ℕ)
    (W : Finset X) {d : ℕ} (T : ProbabilityTree X d) (hbad : ¬Good p m W T) :
    1 < treePotential p m W T := by
  induction T generalizing m with
  | leaf => simp only [Good, not_true_eq_false] at hbad
  | @node d B inst ν hν A child ih =>
      simp only [treePotential]
      simp only [Good] at hbad
      apply one_lt_nodePotential_of_bad (m 0) _ _ _
        (fun b => Good p (fun j => m (j + 1)) W (child b))
      · exact fun b => successfulTargetMass_nonneg ν A hp.le _ W b
      · exact fun b => treePotential_nonneg hp.le _ W (child b)
      · exact localFailureMass_add_successfulTargetMass ν A hν hp (m 0) W
      · exact fun b hb => ih b _ hb
      · exact lt_of_not_ge hbad

omit [Fintype X] in
/-- The potential only inspects the labels belonging to the fixed subtree. -/
theorem treePotential_dependsOnlyOn (p : ℝ) (m : ℕ → ℕ) {d : ℕ}
    (T : ProbabilityTree X d) : DependsOnlyOn T.support (fun W => treePotential p m W T) := by
  induction T generalizing m with
  | leaf => intro W V _; simp only [treePotential]
  | @node d B inst ν hν A child ih =>
      intro W V hWV
      have hd := ((localFailureMass_dependsOnlyOn ν A p (m 0)).mono
        (ProbabilityTree.labels_support_subset ν hν A child)) W V hWV
      have ht (b : B) := ((successfulTargetMass_dependsOnlyOn ν A p (m 0) b).mono
        (ProbabilityTree.labels_support_subset ν hν A child)) W V hWV
      have hc (b : B) := ((ih b (fun j => m (j + 1))).mono
        (ProbabilityTree.child_support_subset ν hν A child b)) W V hWV
      dsimp only at hd ht hc
      simp only [treePotential, nodePotential]
      rw [hd]
      congr 2
      apply Finset.sum_congr rfl
      intro b _
      rw [ht b, hc b]

omit [Fintype X] in
/-- Path disjointness makes a descendant potential insensitive to its
incoming label; this is the locality needed by the change of measure. -/
theorem child_treePotential_dependsOutside {d : ℕ} {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d)
    (hdis : (ProbabilityTree.node B ν hν A child).IsDisjoint)
    (p : ℝ) (m : ℕ → ℕ) (b : B) :
    DependsOutside (A b) (fun W => treePotential p m W (child b)) :=
  ProbabilityTree.child_dependsOutside hdis b (treePotential_dependsOnlyOn p m (child b))

theorem bad_probability_le_expected_treePotential {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (m : ℕ → ℕ) {d : ℕ} (T : ProbabilityTree X d) :
    bernoulliProbability p (fun W => ¬Good p m W T) ≤
      bernoulliExpectation p (fun W => treePotential p m W T) := by
  exact (bernoulliLaw p hp.le hp1).prob_le_expectation (fun W => ¬Good p m W T)
    (fun W => treePotential p m W T) (fun W => treePotential_nonneg hp.le m W T)
    (fun W hW => (one_lt_treePotential_of_not_good hp m W T hW).le)

omit [Fintype X] in
private theorem localFailureMass_eq_probability {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    {p : ℝ} (hp : 0 < p) (m : ℕ) (W : Finset X) :
    localFailureMass ν A p m W =
      (resamplingLaw ν A p W hν hp).prob (fun cb => LocalFailure ν A p m W cb.1 cb.2) := by
  simp only [localFailureMass, FiniteLaw.prob, resamplingLaw_weight, Fintype.sum_prod_type]
  exact Finset.sum_comm

omit [Fintype X] in
theorem successfulTargetMass_le_cutoff {B : Type} [Fintype B]
    (ν : FiniteLaw B) (A : B → Finset X) {p : ℝ} (hp : 0 ≤ p)
    (m : ℕ) (W : Finset X) (b : B) :
    successfulTargetMass ν A p m W b ≤
      cutoffTargetMass ν A p (Real.exp (-10 * (m : ℝ))) W b := by
  unfold successfulTargetMass cutoffTargetMass
  apply Finset.sum_le_sum
  intro c _
  by_cases hsuccess : LocalSuccess ν A p m W c b
  · have hcut : Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A p (resamplingY A W c) :=
      hsuccess.1
    simp only [ite_eq_left hsuccess, ite_eq_left hcut, le_refl]
  · simp only [ite_eq_right hsuccess]
    split_ifs
    · exact resamplingWeight_nonneg ν A hp W (c, b)
    · exact le_rfl

theorem treePotential_expectation_node_le {d : ℕ} {B : Type} [Fintype B]
    (ν : FiniteLaw B) (hν : ν.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d) (m : ℕ → ℕ)
    {p a : ℝ} (hp : 0 < p) (hp1 : p < 1) (ha : 0 ≤ a)
    (hspread : IsSpread ν A a) (hm : 1 ≤ m 0)
    (hsize : ∀ b, (A b).card ≤ m 0) (hsmall : a / p ≤ Real.exp (-50))
    (hdis : (ProbabilityTree.node B ν hν A child).IsDisjoint) :
    bernoulliExpectation p (fun W => treePotential p m W (ProbabilityTree.node B ν hν A child)) ≤
      Real.exp (-8 * (m 0 : ℝ)) + Real.exp (12 * (m 0 : ℝ)) *
        ν.expectation (fun b => bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b))) := by
  simp only [treePotential]
  apply bernoulliExpectation_nodePotential_le p (m 0) ν
  · have h := local_failure_bound ν A hν hp hp1 (m 0) hm hsize hspread ha hsmall
    simpa only [← localFailureMass_eq_probability ν hν A hp (m 0)] using h
  · intro b
    exact outside_change_of_measure_of_le ν A hp hp1.le ha hspread (m 0) b (hsize b) hsmall
      (fun W => treePotential p (fun j => m (j + 1)) W (child b))
      (fun W => treePotential_nonneg hp.le _ W (child b))
      (child_treePotential_dependsOutside ν hν A child hdis p _ b)
      (fun W => successfulTargetMass ν A p (m 0) W b)
      (fun W => successfulTargetMass_le_cutoff ν A hp.le (m 0) W b)

theorem treePotential_expectation_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50)) :
    bernoulliExpectation p (fun W => treePotential p m W T) ≤ potentialEnvelope d m := by
  induction T generalizing m a with
  | leaf => simp [treePotential, potentialEnvelope, bernoulliExpectation]
  | @node d B inst ν hν A child ih =>
      have hnode := treePotential_expectation_node_le ν hν A child m hp hp1
        (ha 0 (by omega)) hspread.1 (hm 0 (by omega)) hcap.1 (hsmall 0 (by omega)) hdis
      have hchild (b : B) : bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b)) ≤
          potentialEnvelope d (fun j => m (j + 1)) := by
        apply ih b (fun j => m (j + 1)) (fun j => a (j + 1)) (hdis.2 b) (hcap.2 b) (hspread.2 b)
        · intro j hj
          exact hm (j + 1) (by omega)
        · intro j hj
          exact ha (j + 1) (by omega)
        · intro j hj
          exact hsmall (j + 1) (by omega)
      have havg : ν.expectation (fun b => bernoulliExpectation p
          (fun W => treePotential p (fun j => m (j + 1)) W (child b))) ≤
          potentialEnvelope d (fun j => m (j + 1)) := by
        unfold FiniteLaw.expectation
        calc
          _ ≤ ∑ b, ν.weight b * potentialEnvelope d (fun j => m (j + 1)) :=
            Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hchild b) (ν.nonneg b))
          _ = _ := by rw [← Finset.sum_mul, ν.total, one_mul]
      exact hnode.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left havg (Real.exp_pos _).le))

/-- One simultaneous reduction fails with probability strictly below one
quarter under the geometric level-capacity assumptions. -/
theorem root_bad_probability_lt_one_quarter {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50))
    (hgrowth : ∀ j, j + 1 < d → 16 * m j ≤ m (j + 1)) :
    bernoulliProbability p (fun W => ¬Good p m W T) < 1 / 4 := by
  have hbound := (bad_probability_le_expected_treePotential hp hp1.le m T).trans
    (treePotential_expectation_le hp hp1 m a T hdis hcap hspread hm ha hsmall)
  rw [potentialEnvelope_eq_sum] at hbound
  exact hbound.trans_lt (capacity_failure_sum_lt_one_quarter m d hm hgrowth)

theorem reduction_good_probability_ge {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (m : ℕ → ℕ) (a : ℕ → ℝ) {d : ℕ} (T : ProbabilityTree X d)
    (hdis : T.IsDisjoint) (hcap : T.HasCapacities m) (hspread : T.HasSpread a)
    (hm : ∀ j, j < d → 1 ≤ m j) (ha : ∀ j, j < d → 0 ≤ a j)
    (hsmall : ∀ j, j < d → a j / p ≤ Real.exp (-50))
    (hgrowth : ∀ j, j + 1 < d → 16 * m j ≤ m (j + 1)) :
    3 / 4 ≤ bernoulliProbability p (fun W => Good p m W T) := by
  have hbad := root_bad_probability_lt_one_quarter hp hp1 m a T
    hdis hcap hspread hm ha hsmall hgrowth
  have hcompl := (bernoulliLaw (X := X) p hp.le hp1.le).prob_compl (fun W => Good p m W T)
  change bernoulliProbability p (fun W => ¬Good p m W T) =
    1 - bernoulliProbability p (fun W => Good p m W T) at hcompl
  linarith

end Trees

end LeanBlast.SecondKahnKalai

end

end OAI
