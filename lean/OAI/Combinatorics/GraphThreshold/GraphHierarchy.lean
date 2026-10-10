import OAI.Combinatorics.GraphThreshold.Basic
import OAI.Combinatorics.GraphThreshold.ProbabilityTree
import OAI.Combinatorics.GraphThreshold.CopyOrbits
import OAI.Combinatorics.GraphThreshold.Predecessor
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI

/-! The finite hierarchy and the actual tree of extensions used in the graph
application. Histories are represented by the probability tree's dependent
paths; equal set labels do not identify distinct histories. -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

/-- A reversed predecessor chain, with its first term empty and last term the
given set. The relation records the actual rule used to select predecessors. -/
structure SetHierarchy {X : Type*} [DecidableEq X]
    (R : Finset X → Finset X → Prop) (H : Finset X) where
  depth : ℕ
  stage : ℕ → Finset X
  first : stage 0 = ∅
  last : stage depth = H
  nested : ∀ i, i < depth → stage i ⊆ stage (i + 1)
  sparse : ∀ i, i < depth → 17 * (stage i).card < (stage (i + 1)).card
  selected : ∀ i, i < depth → R (stage i) (stage (i + 1))

namespace SetHierarchy

variable {X : Type*} [DecidableEq X]
variable {R : Finset X → Finset X → Prop} {H : Finset X}

theorem stage_subset_stage (h : SetHierarchy R H) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ h.depth) : h.stage i ⊆ h.stage j := by
  induction j, hij using Nat.le_induction with
  | base => exact Subset.rfl
  | succ j hij ih =>
      exact (ih (by omega)).trans (h.nested j (by omega))

theorem stage_subset (h : SetHierarchy R H) {i : ℕ} (hi : i ≤ h.depth) :
    h.stage i ⊆ H := by
  simpa only [h.last] using h.stage_subset_stage hi (le_refl h.depth)

theorem depth_pos (h : SetHierarchy R H) (hH : H.Nonempty) : 0 < h.depth := by
  by_contra hn
  have hd : h.depth = 0 := by omega
  have : H = ∅ := by rw [← h.last, hd, h.first]
  simp [this] at hH

/-- The number of new elements on a level of the hierarchy. -/
def capacity (h : SetHierarchy R H) (i : ℕ) : ℕ :=
  (h.stage (i + 1)).card - (h.stage i).card

theorem capacity_pos (h : SetHierarchy R H) {i : ℕ} (hi : i < h.depth) :
    0 < h.capacity i := by
  have hs := h.sparse i hi
  unfold capacity
  omega

theorem capacity_growth (h : SetHierarchy R H) {i : ℕ} (hi : i + 1 < h.depth) :
    16 * h.capacity i ≤ h.capacity (i + 1) := by
  have hs := h.sparse (i + 1) hi
  unfold capacity
  omega

theorem capacity_le (h : SetHierarchy R H) {i : ℕ} (hi : i < h.depth) :
    h.capacity i ≤ H.card := by
  exact (Nat.sub_le _ _).trans (Finset.card_le_card (h.stage_subset (by omega)))

end SetHierarchy

/-- Strict cardinal descent constructs a finite hierarchy; no chain or tree is
assumed as an input. The predecessor hypotheses are needed only inside `H`. -/
theorem exists_setHierarchy {X : Type*} [DecidableEq X]
    (R : Finset X → Finset X → Prop) (H : Finset X)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I) :
    Nonempty (SetHierarchy R H) := by
  have aux : ∀ m : ℕ, ∀ I : Finset X, I.card = m → I ⊆ H →
      Nonempty (SetHierarchy R I) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro I hcard hIH
      by_cases hI : I = ∅
      · subst I
        exact ⟨{
          depth := 0
          stage := fun _ => ∅
          first := rfl
          last := rfl
          nested := by omega
          sparse := by omega
          selected := by omega }⟩
      · obtain ⟨S, hSI, hsmall, hRSI⟩ := hpred I hIH (Finset.nonempty_iff_ne_empty.mpr hI)
        have hlt : S.card < m := by omega
        obtain ⟨a⟩ := ih S.card hlt S rfl (hSI.trans hIH)
        refine ⟨{
          depth := a.depth + 1
          stage := fun i => if i ≤ a.depth then a.stage i else I
          first := by simpa using a.first
          last := by simp
          nested := ?_
          sparse := ?_
          selected := ?_ }⟩
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.nested i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hSI
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.sparse i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hsmall
        · intro i hi
          by_cases hik : i < a.depth
          · simpa only [ite_eq_left (show i ≤ a.depth by omega),
              ite_eq_left (show i + 1 ≤ a.depth by omega)] using a.selected i hik
          · have hik' : i = a.depth := by omega
            subst i
            simpa only [ite_eq_left (le_refl a.depth),
              ite_eq_right (show ¬a.depth + 1 ≤ a.depth by omega), a.last] using hRSI
  exact aux H.card H rfl Subset.rfl

section OrbitTrees

variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

/-- A conditional containment-ratio estimate is exactly spreadness of the
added set. Requests intersecting the existing set have probability zero. -/
theorem extensionLaw_isSpread_of_ratio (I S : Finset X)
    (hp : 0 < containmentProb G I S) (σ : ℝ) (hσ : 0 ≤ σ)
    (hratio : ∀ J : Finset X, J.Nonempty → Disjoint S J →
      containmentProb G I (S ∪ J) / containmentProb G I S ≤ σ ^ J.card) :
    IsSpread (extensionLaw G I S hp) (fun b => b.val.val \ S) σ := by
  intro J hJ
  by_cases hd : Disjoint J S
  · rw [extensionLaw_added_prob G I S J hp hd]
    exact hratio J hJ hd.symm
  · rw [extensionLaw_added_prob_eq_zero G I S J hp hd]
    exact pow_nonneg hσ _

/-- The actual extension tree. At each node its children are all distinct
copies of the next set containing the current copy, with their uniform law.
The dependent path type retains the entire sequence of choices. -/
def orbitExtensionTree : (d : ℕ) → (A : ℕ → Finset X) →
    (∀ i, i < d → A i ⊆ A (i + 1)) →
    (S0 : Finset X) → S0 ∈ copyOrbit G (A 0) → ProbabilityTree X d
  | 0, _, _, _, _ => .leaf
  | d + 1, A, hnested, S0, hS0 =>
      let hp := containmentProb_pos_of_copy_subset G (hnested 0 (by omega)) hS0
      .node (ExtensionCopy G (A 1) S0)
        (extensionLaw G (A 1) S0 hp)
        (extensionLaw_isPositive G (A 1) S0 hp)
        (fun b => b.val.val \ S0)
        (fun b => orbitExtensionTree d (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property)

/-- No element already present at a node occurs anywhere below it. -/
theorem orbitExtensionTree_support_disjoint (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    Disjoint S0 (orbitExtensionTree G d A hnested S0 hS0).support := by
  induction d generalizing A S0 with
  | zero => simp [orbitExtensionTree, ProbabilityTree.support]
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.support,
        Finset.disjoint_biUnion_right, Finset.mem_univ, forall_true_left,
        Finset.disjoint_union_right]
      intro b
      constructor
      · exact Finset.disjoint_left.mpr (fun x hx hxs => (Finset.mem_sdiff.mp hxs).2 hx)
      · exact (ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property).mono_left
          b.property

/-- Every constructed tree has the strong recursive disjointness property. -/
theorem orbitExtensionTree_isDisjoint (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).IsDisjoint := by
  induction d generalizing A S0 with
  | zero => trivial
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.IsDisjoint]
      constructor
      · intro b
        exact (orbitExtensionTree_support_disjoint G d (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property).mono_left
          Finset.sdiff_subset
      · intro b
        exact ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property

/-- Adding a path's labels to its starting copy recovers an actual terminal
copy. In particular an empty root gives an actual copy as its path union. -/
theorem orbitExtensionTree_pathUnion (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0))
    (p : (orbitExtensionTree G d A hnested S0 hS0).Path) :
    S0 ∪ (orbitExtensionTree G d A hnested S0 hS0).pathUnion p ∈
      copyOrbit G (A d) := by
  induction d generalizing A S0 with
  | zero => simpa only [orbitExtensionTree, ProbabilityTree.pathUnion, Finset.union_empty] using hS0
  | succ d ih =>
      rcases p with ⟨b, p⟩
      have hp := ih (fun i => A (i + 1))
        (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property p
      simpa only [orbitExtensionTree, ProbabilityTree.pathUnion, ← Finset.union_assoc,
        Finset.union_sdiff_of_subset b.property] using hp

/-- Every arc has exactly the cardinal difference of its two abstract stages,
so these differences are valid capacities at every node of the tree. -/
theorem orbitExtensionTree_hasCapacities (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).HasCapacities
      (fun i => (A (i + 1)).card - (A i).card) := by
  induction d generalizing A S0 with
  | zero => trivial
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.HasCapacities]
      constructor
      · intro b
        rw [Finset.card_sdiff_of_subset b.property,
          card_eq_of_mem_copyOrbit G b.val.property, card_eq_of_mem_copyOrbit G hS0]
      · intro b
        exact ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega)) b.val.val b.val.property

/-- Local conditional containment ratios give spread at every node, including
nodes reached through different histories with the same current copy. -/
theorem orbitExtensionTree_hasSpread (σ : ℝ) (hσ : 0 ≤ σ)
    (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (hratio : ∀ i, i < d → ∀ S0 ∈ copyOrbit G (A i),
      ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G (A (i + 1)) (S0 ∪ J) /
          containmentProb G (A (i + 1)) S0 ≤ σ ^ J.card)
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).HasSpread (fun _ => σ) := by
  induction d generalizing A S0 with
  | zero => trivial
  | succ d ih =>
      simp only [orbitExtensionTree, ProbabilityTree.HasSpread]
      constructor
      · exact extensionLaw_isSpread_of_ratio G (A 1) S0 _ σ hσ
          (hratio 0 (by omega) S0 hS0)
      · intro b
        exact ih (fun i => A (i + 1))
          (fun i hi => hnested (i + 1) (by omega))
          (fun i hi => hratio (i + 1) (by omega)) b.val.val b.val.property

/-- The constructive assembly from a strict predecessor rule. In particular,
the tree and its chain are outputs, not hypotheses. The concrete maximizing
rule below discharges the two local predecessor requirements. -/
theorem exists_spread_orbit_tree_of_predecessors
    (H : Finset X) (hH : H.Nonempty) (σ : ℝ) (hσ : 0 ≤ σ)
    (R : Finset X → Finset X → Prop)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I)
    (hratio : ∀ I, I ⊆ H → ∀ S, R S I →
      ∀ S0 ∈ copyOrbit G S, ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G I (S0 ∪ J) / containmentProb G I S0 ≤ σ ^ J.card) :
    ∃ k : ℕ, ∃ m : ℕ → ℕ, ∃ T : ProbabilityTree X k,
      0 < k ∧ T.IsDisjoint ∧ T.HasCapacities m ∧ T.HasSpread (fun _ => σ) ∧
      (∀ i, i < k → 0 < m i) ∧
      (∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) ∧
      m (k - 1) ≤ H.card ∧
      ∀ p : T.Path, T.pathUnion p ∈ copyOrbit G H := by
  obtain ⟨a⟩ := exists_setHierarchy R H hpred
  have hk : 0 < a.depth := a.depth_pos hH
  have hroot : (∅ : Finset X) ∈ copyOrbit G (a.stage 0) := by
    rw [a.first]
    exact self_mem_copyOrbit G ∅
  let T := orbitExtensionTree G a.depth a.stage a.nested ∅ hroot
  refine ⟨a.depth, a.capacity, T, hk,
    orbitExtensionTree_isDisjoint G _ _ _ _ _,
    orbitExtensionTree_hasCapacities G _ _ _ _ _, ?_,
    (fun i hi => a.capacity_pos hi), (fun i hi => a.capacity_growth hi),
    a.capacity_le (by omega), ?_⟩
  · apply orbitExtensionTree_hasSpread G σ hσ
    intro i hi S0 hS0 J hJ hd
    exact hratio (a.stage (i + 1)) (a.stage_subset (by omega))
      (a.stage i) (a.selected i hi) S0 hS0 J hJ hd
  · intro p
    simpa only [Finset.empty_union, a.last] using
      orbitExtensionTree_pathUnion G a.depth a.stage a.nested ∅ hroot p

theorem exists_spread_orbit_tree (H : Finset X) (q : ℝ) (hq : 0 < q)
    (hH : H.Nonempty)
    (hE : ∀ U : Finset X, U ⊆ H → U.Nonempty →
      (1 / 2 : ℝ) ≤ (orbitCount G U : ℝ) * q ^ U.card) :
    ∃ k : ℕ, ∃ m : ℕ → ℕ, ∃ T : ProbabilityTree X k,
      0 < k ∧ T.IsDisjoint ∧ T.HasCapacities m ∧
      T.HasSpread (fun _ => 128 * q) ∧
      (∀ i, i < k → 0 < m i) ∧
      (∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) ∧
      m (k - 1) ≤ H.card ∧
      ∀ p : T.Path, T.pathUnion p ∈ copyOrbit G H := by
  apply exists_spread_orbit_tree_of_predecessors G H hH (128 * q) (by positivity)
    (fun S I => S = maximizingPredecessor G I (128 * q))
  · intro I hIH hI
    refine ⟨maximizingPredecessor G I (128 * q),
      maximizingPredecessor_subset G I (128 * q), ?_, rfl⟩
    exact maximizingPredecessor_small G I hI hq
      (fun U hUI hU => hE U (hUI.trans hIH) hU)
  · intro I _ S hS S0 hS0 J _ hd
    subst S
    exact predecessor_conditional_ratio_le G I (by positivity) hS0 hd

end OrbitTrees

end LeanBlast.SecondKahnKalai

end

end OAI
