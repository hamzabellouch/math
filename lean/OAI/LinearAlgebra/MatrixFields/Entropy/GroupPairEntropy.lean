import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.GroupPairWindows
import OAI.LinearAlgebra.MatrixFields.Parameters.GroupSelectionParameters

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem sum_conditionalCenter_entropy {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (p : FiniteLaw A) (f : A → B) :
    (∑ b, (p.map f).mass b * finiteEntropy
      (conditionalCenter f b p.mass ((p.map f).mass b))) =
        finiteEntropy p.mass - finiteEntropy (p.map f).mass := by
  have ht (b : B) :
      (p.map f).mass b * finiteEntropy
        (conditionalCenter f b p.mass ((p.map f).mass b)) =
      (p.map f).mass b * finiteEntropy (p.conditional f b).mass := by
    by_cases hz : (p.map f).mass b = 0
    · simp only [hz, zero_mul]
    · congr 1
      congr 1
      funext a
      simp only [conditionalCenter, FiniteLaw.conditional, dite_eq_right hz]
      split_ifs <;> simp
  simp_rw [ht]
  have he := p.entropy_eq_map_add_conditional f
  linarith

variable {K tick : ℕ} {sigma : Placement}

theorem baseSize_eq_parentBase_mul_sideMass (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    (baseSize (base allocation sigma side) (h, k) : ℝ) =
      (parentBase allocation h : ℝ) *
        JointPopulationRates.sideMass (orderLaw h).mass (sigma side) k := by
  simp only [baseSize, base, JointPopulationCompatibility.classCounts,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, JointPopulationRates.sideMass,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : JointPopulation.shapeSide (sigma side) u = k
  · simp only [hu, ite_true]
    exact jointCounts_cast allocation 1 h.val.val u
  · simp only [hu, ite_false, mul_zero]

theorem classMass_eq_sideMass (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (c : Class (K := K) (tick := tick) sigma) :
    classMass allocation sigma side c =
      JointPopulationRates.sideMass (orderLaw c.1).mass (sigma side) c.2 := by
  rcases c with ⟨h, k⟩
  unfold classMass
  rw [baseSize_eq_parentBase_mul_sideMass]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast (parentBase_pos allocation h).ne')

theorem nativePair_weight_marginal {K : ℕ} (w : Work K) (side : Fin 3)
    (hs : w.stage ≠ 2) :
    ((nativePairLaw w side).map (fun a => weightCode w a.1)).mass =
      canonicalSideMass w side := by
  cases w with
  | stageA h =>
      rw [canonicalSideMass_stageA]
      exact congrArg FiniteLaw.mass
        (AllFieldPairMarginals.stageAPairLaw_leftWeight_marginal _ h.property side)
  | stageB h =>
      rw [canonicalSideMass_stageB]
      exact congrArg FiniteLaw.mass
        (AllFieldPairMarginals.stageBPairLaw_leftWeight_marginal _ h.property side)
  | stageC h => exact False.elim (hs rfl)

theorem orderPair_weight_marginal (h : ActiveOrder K tick sigma) (side : Fin 3)
    (hs : h.val.val.1.stage ≠ 2) :
    ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).map
      (fun a => weightCode h.val.val.1 a.1)).mass =
      JointPopulationRates.sideMass (orderLaw h).mass (sigma side) := by
  rw [nativePair_weight_marginal _ _ hs]
  have hm := placedLaw_priority_sideMass h.val.val side
  rw [h.property] at hm
  exact hm.symm

theorem q_eq_native_conditionalCenter (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (c : Class (K := K) (tick := tick) sigma)
    (hs : c.1.val.val.1.stage ≠ 2) :
    q allocation sigma side c = conditionalCenter
      (fun a => weightCode c.1.val.val.1 a.1) c.2
      (nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).mass
      (((nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).map
        (fun a => weightCode c.1.val.val.1 a.1)).mass c.2) := by
  rw [q_eq_conditionalCenter allocation sigma side c hs, classMass_eq_sideMass,
    orderPair_weight_marginal _ _ hs]
  have hp : parentPair allocation sigma side c.1 =
      (nativePairLaw c.1.val.val.1 (c.1.val.val.1.priority side)).mass := by
    funext a
    rw [parentPair_eq_native, orderPairMixture_eq_native]
  rw [hp]

theorem history_pair_entropy_of_sharing (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2) :
    (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
      finiteEntropy (q allocation sigma side (h, k))) =
      (parentBase allocation h : ℝ) *
        (finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
          finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))) := by
  have hq (k : Fin 17) := q_eq_native_conditionalCenter allocation sigma side (h, k) hs
  simp_rw [baseSize_eq_parentBase_mul_sideMass, hq, mul_assoc]
  rw [← Finset.mul_sum]
  simpa only [orderPair_weight_marginal h side hs] using
    congrArg (fun x : ℝ => (parentBase allocation h : ℝ) * x)
      (sum_conditionalCenter_entropy
        (nativePairLaw h.val.val.1 (h.val.val.1.priority side))
        (fun a => weightCode h.val.val.1 a.1))

theorem history_pair_entropy_of_ordinary (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage = 2) :
    (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
      finiteEntropy (q allocation sigma side (h, k))) = 0 := by
  have : Subsingleton (Statistic h.val) := by
    change Subsingleton h.val.val.1.Statistic
    cases he : h.val.val.1 with
    | stageA a => simp [he, Work.stage] at hs
    | stageB a => simp [he, Work.stage] at hs
    | stageC a => dsimp [Work.Statistic]; infer_instance
  apply Finset.sum_eq_zero
  intro k _
  by_cases hz : baseSize (base allocation sigma side) (h, k) = 0
  · simp only [hz, Nat.cast_zero, zero_mul]
  · have hq : q allocation sigma side (h, k) = fun _ => 1 := by
      funext a
      exact q_eq_one_of_subsingleton allocation sigma side (h, k)
        (Nat.pos_of_ne_zero hz) a
    simp only [hq, finiteEntropy, entropyTerm, Real.log_one, mul_zero,
      Finset.sum_const_zero]

theorem pairReferenceEntropy_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) :
    pairReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
      (q allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (if h.val.val.1.stage ≠ 2 then
          finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
            finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))
        else 0) := by
  unfold pairReferenceEntropy
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hs : h.val.val.1.stage ≠ 2
  · rw [ite_eq_left hs]
    exact history_pair_entropy_of_sharing allocation sigma side h hs
  · rw [ite_eq_right hs, mul_zero]
    exact history_pair_entropy_of_ordinary allocation sigma side h (not_not.mp hs)

theorem baseEntropy_eq (allocation : Allocation) (sigma : Placement) (side : Fin 3) :
    baseEntropy (base (K := K) (tick := tick) allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (finiteEntropy (orderLaw h).mass -
          finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))) := by
  unfold baseEntropy
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  have hb (k : Fin 17) : base allocation sigma side (h, k) =
      JointConditionalCountEntropy.classCounts (Counts allocation 1 sigma h)
        (JointPopulation.shapeSide (sigma side)) k := by
    funext u
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k
    · simp only [base, JointPopulationCompatibility.classCounts,
        JointConditionalCountEntropy.classCounts, hu, ite_true]
    · simp only [base, JointPopulationCompatibility.classCounts,
        JointConditionalCountEntropy.classCounts, hu, ite_false]
  have hs (k : Fin 17) : baseSize (base allocation sigma side) (h, k) =
      JointConditionalCountEntropy.classSize (Counts allocation 1 sigma h)
        (JointPopulation.shapeSide (sigma side)) k := by
    simp only [baseSize, JointConditionalCountEntropy.classSize, hb k]
  have hm : ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass =
      JointPopulationRates.sideMass (orderLaw h).mass (sigma side) := by
    funext k
    rw [FiniteLaw.map_mass]
    rfl
  have he := JointConditionalCountEntropy.sum_classSize_mul_entropy_of_law
    (Counts allocation 1 sigma h) (JointPopulation.shapeSide (sigma side))
    (orderLaw h) (parentBase allocation h : ℝ)
    (fun u => jointCounts_cast allocation 1 h.val.val u)
  rw [hm] at he
  simpa only [hs, hb] using he

def observedEntropy (h : ActiveOrder K tick sigma) (side : Fin 3) : ℝ :=
  if h.val.val.1.stage ≠ 2 then
    finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass
  else finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))

theorem baseEntropy_sub_pairReferenceEntropy (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) :
    baseEntropy (base (K := K) (tick := tick) allocation sigma side) -
      pairReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (q allocation sigma side) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (finiteEntropy (orderLaw h).mass - observedEntropy h side) := by
  rw [baseEntropy_eq, pairReferenceEntropy_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  unfold observedEntropy
  split_ifs <;> ring

end MatrixMultiplication.AllFieldGroupPairEntropy

end
end

end MatrixAllFields

end OAI
