import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.PairEntropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.DegreeLaws
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.GroupedEntropyEmbedding
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.ProjectedGroupEntropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.BranchDesignation
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.BranchLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.NativeGroupedRates

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupProjectedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees
open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls
open JointCompatibilityIncidence JointGroupedEntropyEmbedding JointGroupedEntropyPartition
open AllFieldGroupBranchDesignation AllFieldGroupBranchLaws AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section Kernel

variable {U V G A : Type*} [Fintype U] [Fintype V] [Fintype G] [Fintype A]

theorem groupedEntropy_congr_law_on_support (p : U → ℝ) (group : U → G)
    (q q' : U → A → ℝ) (hq : ∀ u, p u ≠ 0 → q u = q' u) :
    groupedEntropy p group q = groupedEntropy p group q' := by
  have he (g : G) : groupLaw p group q g = groupLaw p group q' g := by
    funext a
    unfold groupLaw
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    by_cases hp : p u = 0
    · simp only [hp, zero_mul]
    · rw [hq u hp]
  simp only [groupedEntropy, he]

theorem groupedEntropy_designated_pushforward (p : U → ℝ) (f : U → V)
    (hf : Function.Injective f) (d : V → Prop) (d' : U → Prop)
    (hd : ∀ u, d (f u) ↔ d' u) (q : V → A → ℝ) (q' : U → A → ℝ)
    (hq : ∀ u, p u ≠ 0 → q (f u) = q' u) :
    groupedEntropy (pushforwardWeight p f) (designatedGroup d) q =
      groupedEntropy p (designatedGroup d') q' := by
  rw [groupedEntropy_pushforward]
  have hg : designatedGroup d ∘ f = Option.map f ∘ designatedGroup d' := by
    funext u
    by_cases hu : d' u
    · simp [designatedGroup, (hd u).mpr hu, hu]
    · simp [designatedGroup, mt (hd u).mp hu, hu]
  rw [hg, groupedEntropy_label_injective (Option.map f) (Option.map_injective hf)]
  exact groupedEntropy_congr_law_on_support p _ _ q' hq

theorem groupedEntropy_const_one (p : U → ℝ) (group : U → G) :
    groupedEntropy p group (fun _ (_ : A) => 1) = 0 := by
  unfold groupedEntropy
  apply Finset.sum_eq_zero
  intro g _
  by_cases hg : groupMass p group g = 0
  · rw [hg, zero_mul]
  · have he : groupLaw p group (fun _ (_ : A) => 1) g = fun _ => 1 := by
      funext a
      simp only [groupLaw, mul_one]
      exact div_self hg
    rw [he]
    simp [finiteEntropy, entropyTerm]

omit [Fintype V] [Fintype G] in
theorem pushforwardWeight_mask (p : U → ℝ) (f : U → V)
    (weight : V → G) (k : G) :
    (fun v => if weight v = k then pushforwardWeight p f v else 0) =
      pushforwardWeight (fun u => if weight (f u) = k then p u else 0) f := by
  funext v
  unfold pushforwardWeight
  by_cases hv : weight v = k
  · simp only [hv, ite_true]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : f u = v <;> simp [hu, hv]
  · simp only [hv, ite_false]
    symm
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : f u = v <;> simp [hu, hv]

end Kernel

variable {K tick : ℕ} {sigma : Placement}

def maskedBranchMass (h : ActiveOrder K tick sigma) (side : Fin 3) (k : Fin 17)
    (b : h.val.val.1.Branch) : ℝ :=
  if nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k
  then (branchLaw h.val.val.1).mass b else 0

theorem classCounts_cast_eq_pushforward (allocation : Allocation) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (k : Fin 17) :
    (fun u => (base allocation sigma side (h, k) u : ℝ)) =
      fun u => (parentBase allocation h : ℝ) *
        pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) u := by
  have hpmap : (placedLaw h.val.val).mass =
      pushforwardWeight (branchLaw h.val.val.1).mass (branchShape h.val.val) := by
    funext u
    simp only [placedLaw, FiniteLaw.map_mass, pushforwardWeight]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : branchShape h.val.val b = u <;> simp only [hb, ite_true, ite_false]
  have hm : (fun u => if JointPopulation.shapeSide (sigma side) u = k
      then (placedLaw h.val.val).mass u else 0) =
      pushforwardWeight (maskedBranchMass h side k) (branchShape h.val.val) := by
    rw [hpmap]
    funext u
    unfold pushforwardWeight maskedBranchMass
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k
    · simp only [hu, ite_true]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b = k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true]
      · simp only [hb, ite_false]
    · simp only [hu, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro b _
      by_cases hb : branchShape h.val.val b = u
      · have hk : nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b ≠ k := by
          rw [← order_branch_weight h side b, hb]
          exact hu
        simp only [hb, hk, ite_true, ite_false]
      · simp only [hb, ite_false]
  funext u
  change ((if JointPopulation.shapeSide (sigma side) u = k
    then Counts allocation 1 sigma h u else 0 : ℕ) : ℝ) = _
  rw [Nat.cast_ite, Nat.cast_zero]
  rw [← hm]
  by_cases hu : JointPopulation.shapeSide (sigma side) u = k
  · simp only [hu, ite_true]
    exact jointCounts_cast allocation 1 h.val.val u
  · simp only [hu, ite_false, mul_zero]

def branchHalfLaw (w : Work K) (right : Bool) (side : Fin 3)
    (b : w.Branch) (a : w.Statistic) : ℝ :=
  (w.childLaw (halfShape w.parentShape (w.splitShape b) right) (w.priority side) a : ℝ)

theorem class_groupedEntropy_eq_masked (allocation : Allocation) (right : Bool)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
      (designatedGroup (classDesignated right side sigma (h, k)))
      (nativeLaw allocation right side sigma (h, k)) =
      (parentBase allocation h : ℝ) *
        groupedEntropy (maskedBranchMass h side k)
          (designatedGroup (nativeBranchDesignated h.val.val.1 right side))
          (branchHalfLaw h.val.val.1 right side) := by
  rw [classCounts_cast_eq_pushforward, groupedEntropy_mul]
  congr 1
  apply groupedEntropy_designated_pushforward _ _ (branchShape_injective h.val.val)
    _ _ (fun b => designated_branchShape right side h hside b)
  intro b hb
  have hp : (branchLaw h.val.val.1).mass b ≠ 0 := by
    intro hp
    apply hb
    simp only [maskedBranchMass, hp, ite_self]
  exact supportedHalfLaw_branchShape_of_mass_ne_zero allocation right h b hp side

theorem maskedBranchMass_eq_conditional (h : ActiveOrder K tick sigma)
    (side : Fin 3) (k : Fin 17) :
    maskedBranchMass h side k = fun b =>
      ((branchLaw h.val.val.1).map
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side))).mass k *
      ((branchLaw h.val.val.1).conditional
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k).mass b := by
  funext b
  exact ((branchLaw h.val.val.1).map_mass_mul_conditional
    (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) k b).symm

def branchConditionalCost (w : Work K) (side : Fin 3) : ℝ :=
  ∑ k : Fin 17,
    ((branchLaw w).map (nativeSplitWeightCode w (w.priority side))).mass k *
      (groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w false side)) (branchHalfLaw w false side) +
      groupedEntropy ((branchLaw w).conditional
          (nativeSplitWeightCode w (w.priority side)) k).mass
        (designatedGroup (nativeBranchDesignated w true side)) (branchHalfLaw w true side))

theorem history_projected_entropy_eq (allocation : Allocation)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) :
    (∑ k : Fin 17,
      (groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated false side sigma (h, k)))
        (nativeLaw allocation false side sigma (h, k)) +
      groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
        (designatedGroup (classDesignated true side sigma (h, k)))
        (nativeLaw allocation true side sigma (h, k)))) =
      (parentBase allocation h : ℝ) * branchConditionalCost h.val.val.1 side := by
  simp_rw [class_groupedEntropy_eq_masked allocation _ side hside,
    maskedBranchMass_eq_conditional, groupedEntropy_mul]
  simp only [branchConditionalCost, Finset.mul_sum, mul_add]

theorem branchConditionalCost_eq (w : Work K) (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost w side =
      if w.stage ≠ 2 then
        finiteEntropy (nativePairLaw w (w.priority side)).mass - workCapacity w side
      else 0 := by
  cases w with
  | stageA h =>
      have hs : (Work.stageA h).stage ≠ 2 := by change (0 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageA h) =
          AllFieldNativeCapacity.stageASplitLaw (initialShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageA h) ((Work.stageA h).priority side) =
          AllFieldPairConditionalEntropy.stageASplitWeight (initialShape h.val) h.property side := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageA h) right side =
          fun b => AllFieldNativeCapacity.designated (Equiv.refl (Fin 3)) side
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageA h) right side =
          fun b a => (halfLaw
            (halfShape (initialShape h.val) (below (initialShape h.val))[b.val] right)
            side a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      change _ = finiteEntropy (AllFieldNativeCapacity.stageAPairLaw
        (initialShape h.val) h.property side).mass -
          AllFieldNativeCapacity.stageACapacity (initialShape h.val) side
      dsimp only [Work.Branch, Work.Statistic, instFintypeBranch, instFintypeStatistic]
      simpa only [twoHalfConditionalCost, halfShape, Bool.false_eq_true, ite_false, ite_true] using!
        stageA_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageB h =>
      have hs : (Work.stageB h).stage ≠ 2 := by change (1 : Fin 3) ≠ 2; decide
      have hl : branchLaw (Work.stageB h) =
          AllFieldNativeCapacity.stageBSplitLaw (aShape h.val) h.property := rfl
      have hw : nativeSplitWeightCode (Work.stageB h) ((Work.stageB h).priority side) =
          AllFieldPairConditionalEntropy.stageBSplitWeight (aShape h.val) h.property
            (stageBPriority (aShape h.val) side) := by
        funext b
        apply Fin.ext
        rfl
      have hd (right : Bool) : nativeBranchDesignated (Work.stageB h) right side =
          fun b => AllFieldNativeCapacity.designated (stageBPriority (aShape h.val)) side
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right) := by
        funext b
        apply propext
        change (_ ∧ _) ↔ _
        exact ⟨fun hh => hh.2, fun hh => ⟨hs, hh⟩⟩
      have hq (right : Bool) : branchHalfLaw (Work.stageB h) right side =
          fun b a => (littleLaw (aShape h.val)
            (halfShape (aShape h.val) (below (aShape h.val))[b.val] right)
            (stageBPriority (aShape h.val) side) a : ℝ) := rfl
      rw [ite_eq_left hs]
      rw [branchConditionalCost, hl, hw]
      simp_rw [hd, hq]
      change _ = finiteEntropy (AllFieldNativeCapacity.stageBPairLaw
        (aShape h.val) h.property (stageBPriority (aShape h.val) side)).mass -
          AllFieldNativeCapacity.stageBCapacity (aShape h.val) side
      dsimp only [Work.Branch, Work.Statistic, instFintypeBranch, instFintypeStatistic]
      simpa only [twoHalfConditionalCost, halfShape, Bool.false_eq_true, ite_false, ite_true] using!
        stageB_twoHalfConditionalCost_eq_entropy_sub_capacity _ h.property side hside
  | stageC h =>
      rw [ite_eq_right (show ¬ (Work.stageC h).stage ≠ 2 by simp [Work.stage])]
      unfold branchConditionalCost
      have hq (right : Bool) : branchHalfLaw (Work.stageC h) right side =
          fun _ _ => 1 := by
        funext b a
        simp only [branchHalfLaw, Work.childLaw, Rat.cast_one]
      simp only [hq, groupedEntropy_const_one, zero_add, mul_zero, Finset.sum_const_zero]

theorem branchConditionalCost_eq_observed (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hside : side ≠ 0) :
    branchConditionalCost h.val.val.1 side =
      observedEntropy h side - workCapacity h.val.val.1 side := by
  rw [branchConditionalCost_eq _ side hside]
  unfold observedEntropy
  by_cases hs : h.val.val.1.stage ≠ 2
  · rw [ite_eq_left hs, ite_eq_left hs]
  · rw [ite_eq_right hs, ite_eq_right hs]
    have hc : workCapacity h.val.val.1 side = finiteEntropy
        (JointPopulationRates.sideMass (orderLaw h).mass (sigma side)) := by
      rcases h with ⟨⟨⟨w, phi⟩, ht⟩, ho⟩
      cases w with
      | stageA a => exact False.elim (hs (by change (0 : Fin 3) ≠ 2; decide))
      | stageB a => exact False.elim (hs (by change (1 : Fin 3) ≠ 2; decide))
      | stageC a =>
          have hh := AllFieldActiveCapacity.workCapacity_stageC_physical a phi side
          simpa only [ho, orderLaw] using hh
    rw [hc, sub_self]

theorem projected_native_entropy_eq (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (hside : side ≠ 0) :
    projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated false side sigma)
        (groupCap (base allocation sigma side) (classDesignated false side sigma)
          (nativeLaw allocation false side sigma) 0) +
      projectedReferenceEntropy (base (K := K) (tick := tick) allocation sigma side)
        (classDesignated true side sigma)
        (groupCap (base allocation sigma side) (classDesignated true side sigma)
          (nativeLaw allocation true side sigma) 0) =
      ∑ h : ActiveOrder K tick sigma, (parentBase allocation h : ℝ) *
        (observedEntropy h side - workCapacity h.val.val.1 side) := by
  rw [JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    JointProjectedGroupEntropy.projectedReferenceEntropy_eq_sum_counts_groupedEntropy,
    ← Finset.sum_add_distrib, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h _
  rw [history_projected_entropy_eq allocation side hside,
    branchConditionalCost_eq_observed h side hside]

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end

end OAI
