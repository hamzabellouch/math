import OAI.Combinatorics.GraphThreshold.TreeReductionData
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

open scoped BigOperators
open Classical

noncomputable section

namespace LeanBlast.SecondKahnKalai

section RetainedLaw

variable {B X : Type*} [Fintype B] [DecidableEq X]

def retainedMass (w : B → ℝ) (G : B → Prop) : ℝ :=
  ∑ b, if G b then w b else 0

abbrev RetainedIndex (w : B → ℝ) (G : B → Prop) := {b : B // G b ∧ 0 < w b}

theorem sum_retained (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b) (f : B → ℝ) :
    (∑ b : RetainedIndex w G, w b * f b) = ∑ b, if G b then w b * f b else 0 := by
  symm
  apply Finset.sum_congr_set {b | G b ∧ 0 < w b}
  · intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    simp [hb.1]
  · intro b hb
    by_cases hg : G b
    · have hnot : ¬ 0 < w b := fun hpos => hb ⟨hg, hpos⟩
      have hz : w b = 0 := le_antisymm (le_of_not_gt hnot) (hw b)
      simp [hg, hz]
    · simp [hg]

theorem sum_retained_weights (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : RetainedIndex w G, w b) = retainedMass w G := by
  simpa only [mul_one, retainedMass] using sum_retained w G hw (fun _ => 1)

theorem sum_retained_indicator (w : B → ℝ) (G Q : B → Prop) (hw : ∀ b, 0 ≤ w b) :
    (∑ b : RetainedIndex w G, if Q b then w b else 0) =
      ∑ b, if G b ∧ Q b then w b else 0 := by
  simpa only [mul_ite, mul_one, mul_zero, ite_and] using
    sum_retained w G hw (fun b => if Q b then 1 else 0)

/-- The actual normalized child law, after removing all zero-mass targets. -/
def retainedLaw (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) : FiniteLaw (RetainedIndex w G) where
  weight b := w b / retainedMass w G
  nonneg b := div_nonneg (hw b) hpos.le
  total := by
    rw [← Finset.sum_div, sum_retained_weights w G hw]
    exact div_self hpos.ne'

theorem retainedLaw_positive (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) : (retainedLaw w G hw hpos).IsPositive := by
  intro b
  exact div_pos b.property.2 hpos

theorem retainedLaw_prob (w : B → ℝ) (G Q : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) :
    (retainedLaw w G hw hpos).prob (fun b => Q b) =
      (∑ b, if G b ∧ Q b then w b else 0) / retainedMass w G := by
  rw [← sum_retained_indicator w G Q hw, Finset.sum_div]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro b _
  by_cases hq : Q b <;> simp [retainedLaw, hq]

theorem retainedLaw_isSpread (w : B → ℝ) (G : B → Prop) (hw : ∀ b, 0 ≤ w b)
    (hpos : 0 < retainedMass w G) (F : B → Finset X) {a q : ℝ}
    (ha : 0 ≤ a) (hq : 0 < q) (hq1 : q ≤ 1) (hretain : q ≤ retainedMass w G)
    (hnum : ∀ J : Finset X, J.Nonempty →
      (∑ b, if G b ∧ J ⊆ F b then w b else 0) ≤ a ^ J.card) :
    IsSpread (retainedLaw w G hw hpos) (fun b => F b) (a / q) := by
  classical
  intro J hJ
  change (retainedLaw w G hw hpos).prob (fun b => J ⊆ F b.val) ≤ (a / q) ^ J.card
  rw [retainedLaw_prob w G (fun b => J ⊆ F b) hw hpos]
  have hpower : q ^ J.card ≤ q :=
    pow_le_of_le_one hq.le hq1 (Nat.ne_of_gt hJ.card_pos)
  calc
    _ ≤ a ^ J.card / retainedMass w G := by
      apply div_le_div_of_nonneg_right _ hpos.le
      convert hnum J hJ using 1
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : G b ∧ J ⊆ F b <;> simp [hb]
    _ ≤ a ^ J.card / q := div_le_div_of_nonneg_left (pow_nonneg ha _) hq hretain
    _ ≤ a ^ J.card / q ^ J.card :=
      div_le_div_of_nonneg_left (pow_nonneg ha _) (pow_pos hq _) hpower
    _ = (a / q) ^ J.card := (div_pow a q J.card).symm

theorem target_fragment_mass_le_source
    (μ : FiniteLaw B) (A F : B → Finset X) (joint : B × B → ℝ)
    (event : B → B → Prop) (G : B → Prop)
    (hjoint : ∀ c b, 0 ≤ joint (c, b))
    (hsource : ∀ c, ∑ b, joint (c, b) = μ.weight c)
    (hfragment : ∀ c b, 0 < joint (c, b) → F b ⊆ A c) (J : Finset X) :
    (∑ b, if G b ∧ J ⊆ F b then ∑ c, if event c b then joint (c, b) else 0 else 0) ≤
      μ.prob (fun c => J ⊆ A c) := by
  calc
    _ = ∑ b, ∑ c,
        if G b ∧ J ⊆ F b then if event c b then joint (c, b) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : G b ∧ J ⊆ F b <;> simp [hb]
    _ = ∑ c, ∑ b,
        if G b ∧ J ⊆ F b then if event c b then joint (c, b) else 0 else 0 :=
      Finset.sum_comm
    _ ≤ ∑ c, ∑ b, if J ⊆ A c then joint (c, b) else 0 := by
      apply Finset.sum_le_sum
      intro c _
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : G b ∧ J ⊆ F b
      · by_cases he : event c b
        · by_cases hj : 0 < joint (c, b)
          · have hJA : J ⊆ A c := hb.2.trans (hfragment c b hj)
            simp [hb, he, hJA]
          · have hz : joint (c, b) = 0 :=
              le_antisymm (le_of_not_gt hj) (hjoint c b)
            simp [hb, he, hz]
        · simp only [ite_eq_left hb, ite_eq_right he]
          split_ifs <;> linarith [hjoint c b]
      · simp only [ite_eq_right hb]
        split_ifs <;> linarith [hjoint c b]
    _ = μ.prob (fun c => J ⊆ A c) := by
      unfold FiniteLaw.prob
      apply Finset.sum_congr rfl
      intro c _
      by_cases hc : J ⊆ A c <;> simp [hc, hsource]

end RetainedLaw

section Construction

variable {X : Type} [DecidableEq X]

theorem one_sub_exp_neg_nat_pos {m : ℕ} (hm : 0 < m) :
    0 < 1 - Real.exp (-(m : ℝ)) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hm'))

theorem good_retainedMass_pos {d : ℕ} {B : Type} [Fintype B]
    (μ : FiniteLaw B) (hμ : μ.IsPositive) (A : B → Finset X)
    (child : B → ProbabilityTree X d) (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X)
    (hm : 0 < m 0) (hg : Good ρ m W (.node B μ hμ A child)) :
    0 < retainedMass (successfulTargetMass μ A ρ (m 0) W)
      (fun b => Good ρ (fun j => m (j + 1)) W (child b)) := by
  apply lt_of_lt_of_le (one_sub_exp_neg_nat_pos hm)
  simpa only [Good, retainedMass] using hg

/-- Explicit good-node pruning and normalization. The depth is preserved in the
result type. Every retained label is the actual fragment of its original label. -/
def reduceTree (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) : ProbabilityTree X d :=
  match T with
  | .leaf => .leaf
  | @ProbabilityTree.node _ n _B _inst μ hμ A child =>
      let w := successfulTargetMass μ A ρ (m 0) W
      let G := fun b => Good ρ (fun j => m (j + 1)) W (child b)
      have hw : ∀ b, 0 ≤ w b := successfulTargetMass_nonneg μ A hρ.le (m 0) W
      have hp : 0 < retainedMass w G :=
        good_retainedMass_pos μ hμ A child ρ m W (hm 0 (Nat.succ_pos _)) hg
      .node (RetainedIndex w G) (retainedLaw w G hw hp)
        (retainedLaw_positive w G hw hp) (fun b => A b.val \ W)
        (fun b => reduceTree ρ (fun j => m (j + 1)) W (child b.val) hρ
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1)
termination_by structural T

theorem reduceTree_support_subset (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) : (reduceTree ρ m W T hρ hm hg).support ⊆ T.support := by
  induction T generalizing m with
  | leaf => simp [reduceTree, ProbabilityTree.support]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.support]
      intro x hx
      obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hx
      refine Finset.mem_biUnion.mpr ⟨b.val, Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hb).1
      · exact Finset.mem_union_right _
          (ih b.val (fun j => m (j + 1))
            (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1 hb)

theorem reduceTree_hasCapacities (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) :
    (reduceTree ρ m W T hρ hm hg).HasCapacities (fun j => m j / 2) := by
  induction T generalizing m with
  | leaf => simp only [reduceTree, ProbabilityTree.HasCapacities]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.HasCapacities]
      constructor
      · intro b
        exact successfulTargetMass_pos_capacity μ A ρ (m 0) W b.val b.property.2
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1

theorem reduceTree_isDisjoint (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) (hT : T.IsDisjoint) :
    (reduceTree ρ m W T hρ hm hg).IsDisjoint := by
  induction T generalizing m with
  | leaf => simp only [reduceTree, ProbabilityTree.IsDisjoint]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.IsDisjoint]
      constructor
      · intro b
        exact (hT.1 b.val).mono Finset.sdiff_subset
          (reduceTree_support_subset ρ (fun j => m (j + 1)) W (child b.val) hρ
            (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1)
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1 (hT.2 b.val)

theorem reduceTree_path_recovery (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) :
    ∀ q : (reduceTree ρ m W T hρ hm hg).Path,
      ∃ p : T.Path, T.pathUnion p ⊆ W ∪ (reduceTree ρ m W T hρ hm hg).pathUnion q := by
  induction T generalizing m with
  | leaf =>
      intro q
      exact ⟨PUnit.unit, Finset.empty_subset _⟩
  | @node n B inst μ hμ A child ih =>
      rw [reduceTree]
      simp only [ProbabilityTree.Path, ProbabilityTree.pathUnion]
      intro q
      rcases q with ⟨b, q⟩
      obtain ⟨p, hp⟩ := ih b.val (fun j => m (j + 1))
        (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1 q
      refine ⟨⟨b.val, p⟩, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with ha | hc
      · by_cases hw : x ∈ W
        · exact Finset.mem_union_left _ hw
        · exact Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hw⟩))
      · rcases Finset.mem_union.mp (hp hc) with hw | hq
        · exact Finset.mem_union_left _ hw
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ hq)

theorem reduceTree_hasSpread (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) (a : ℕ → ℝ) (ha : ∀ j < d, 0 ≤ a j)
    (hT : T.HasSpread a) :
    (reduceTree ρ m W T hρ hm hg).HasSpread
      (fun j => a j / (1 - Real.exp (-(m j : ℝ)))) := by
  induction T generalizing m a with
  | leaf => simp only [reduceTree, ProbabilityTree.HasSpread]
  | @node n B inst μ hμ A child ih =>
      simp only [reduceTree, ProbabilityTree.HasSpread]
      constructor
      · refine retainedLaw_isSpread (successfulTargetMass μ A ρ (m 0) W)
          (fun b => Good ρ (fun j => m (j + 1)) W (child b))
          (successfulTargetMass_nonneg μ A hρ.le (m 0) W)
          (good_retainedMass_pos μ hμ A child ρ m W (hm 0 (Nat.succ_pos _)) hg)
          (fun b => A b \ W)
          (ha 0 (Nat.succ_pos _))
          (one_sub_exp_neg_nat_pos (hm 0 (Nat.succ_pos _))) ?_ ?_ ?_
        · linarith [Real.exp_pos (-(m 0 : ℝ))]
        · simpa only [retainedMass, Good] using hg
        · intro J hJ
          exact (target_fragment_mass_le_source μ A (fun b => A b \ W)
            (resamplingWeight μ A ρ W) (LocalSuccess μ A ρ (m 0) W)
            (fun b => Good ρ (fun j => m (j + 1)) W (child b))
            (fun c b => resamplingWeight_nonneg μ A hρ.le W (c, b))
            (resampling_source_marginal μ A hμ hρ W)
            (fun c b hp => resamplingFragment_subset_source μ A ρ W c b hp) J).trans
            (hT.1 J hJ)
      · intro b
        exact ih b.val (fun j => m (j + 1))
          (fun j hj => hm (j + 1) (Nat.succ_lt_succ hj)) b.property.1
          (fun j => a (j + 1)) (fun j hj => ha (j + 1) (Nat.succ_lt_succ hj))
          (hT.2 b.val)

end Construction

end LeanBlast.SecondKahnKalai

end

end OAI
