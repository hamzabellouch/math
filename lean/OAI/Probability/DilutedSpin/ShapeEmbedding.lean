import OAI.Probability.DilutedSpin.ActualCharging
import OAI.Probability.DilutedSpin.ColorSymmetry
import OAI.Probability.DilutedSpin.TreeSampleProjection

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

/-- Every old leaf of a prescribed tree has exactly the full kernel path law. -/
theorem leaf_marginal {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (a : S.Leaf) (D : FinitePath Ω n → ℝ) :
    (S.sampleLaw T).expect (fun x => D (S.pathAt a x)) = (KernelTower.law n T).expect D := by
  induction S with
  | leaf => rfl
  | @node n k C ih =>
    rcases T with ⟨μ,K⟩
    rcases a with ⟨i,a⟩
    change (FiniteLaw.pi (fun j => μ.bind (fun z => sampleLaw (C j) (K z)))).expect
      (fun x => D ((x i).1,(C i).pathAt a (x i).2)) = _
    have e := FiniteLaw.expect_pi_marginal
      (fun j => μ.bind (fun z => sampleLaw (C j) (K z))) i
      (fun y => D (y.1,(C i).pathAt a y.2))
    refine e.trans ?_
    erw [FiniteLaw.expect_bind,KernelTower.law_succ_expect]
    apply FiniteLaw.expect_congr
    intro z
    exact ih i (K z) a (fun y => D (z,y))

omit [Fintype Ω] in
lemma pathAt_single (n : ℕ) (a : (single n).Leaf) (x : Sample Ω (single n)) :
    (single n).pathAt a x = singlePath n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨i,a⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change ((x 0).1,pathAt (single n) a (x 0).2) = _
    rw [ih]
    rfl

lemma anchorAt_leaf {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (a : S.Leaf) (E : FinitePath Ω n → ℝ)
    {A : FinitePath Ω n → ℝ} (hA : ∀ y, 0 < A y) :
    anchorAt S T m (Finset.univ.erase a) (S.pathAt) (fun x => E (S.pathAt a x)) A =
      (KernelTower.law n (KernelTower.tilt n T (fun j => m j.succ) (fun y => Real.log (A y)))).expect
        (fun y => E y / A y) := by
  classical
  unfold anchorAt protectedAt
  rw [← leaf_marginal S _ a (fun y => E y / A y)]
  apply FiniteLaw.expect_congr
  intro x
  rw [exp_neg_leafSum_log S A hA]
  have hp := Finset.mul_prod_erase (Finset.univ : Finset S.Leaf)
    (fun b => A (S.pathAt b x)) (Finset.mem_univ a)
  have hn : ∏ b ∈ (Finset.univ : Finset S.Leaf).erase a, A (S.pathAt b x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b _ => ne_of_gt (hA _))
  rw [← hp]
  field_simp

/-- The one-test Taylor coefficient is independent of all unused old leaves.
This justifies the singleton-anchor term in the prescribed-tree identity. -/
theorem anchorCoefficient_leaf {n : ℕ} (S : PrescribedTree n) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : ∀ j : Fin n, m j.succ ≠ 0)
    (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (a : S.Leaf) (D E : FinitePath Ω n → ℝ) (k : ℕ) :
    anchorCoefficient S T m D a (fun x => E (S.pathAt a x)) k =
      anchorCoefficient (single n) T m D (firstLeaf (single n))
        (fun x => E ((single n).pathAt (firstLeaf (single n)) x)) k := by
  unfold anchorCoefficient
  rw [← iteratedFDeriv_anchorAt_diagonal T m hm hroot hend,
      ← iteratedFDeriv_anchorAt_diagonal T m hm hroot hend]
  have he : anchorAt S T m (Finset.univ.erase a) (S.pathAt) (fun x => E (S.pathAt a x)) =ᶠ[nhds (fun _ => 1)]
      anchorAt (single n) T m (Finset.univ.erase (firstLeaf (single n))) (pathAt (single n))
        (fun x => E ((single n).pathAt (firstLeaf (single n)) x)) := by
    filter_upwards [eventually_positive_insertion (n := n) (Ω := Ω) (A := fun _ => 1) (by simp)] with A hA
    rw [anchorAt_leaf S T m a E hA,anchorAt_leaf (single n) T m _ E hA]
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators

/-- Inclusion of an exact prescribed splitting matrix into the actual history
geometry. This is an inclusion of leaf POSITIONS, not of sampled configurations. -/
structure SplitMap {n : ℕ} (T S : PrescribedTree n) where
  leaf : T.Leaf → S.Leaf
  split : ∀ a b, splitDepth S (leaf a) (leaf b) = splitDepth T a b

namespace SplitMap
variable {n : ℕ} {T S : PrescribedTree n}

lemma injective (f : SplitMap T S) : Function.Injective f.leaf := by
  intro a b h
  apply (splitDepth_eq_height T a b).mp
  rw [← f.split,h,splitDepth_self]

variable {k l : ℕ+} {C : Fin k → PrescribedTree n} {D : Fin l → PrescribedTree n}

def childIndex (f : SplitMap (.node k C) (.node l D)) (i : Fin k) : Fin l :=
  (f.leaf ⟨i,firstLeaf (C i)⟩).1

lemma rootAgreement (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    (f.leaf ⟨i,a⟩).1 = f.childIndex i := by
  by_contra h
  have hz := (splitDepth_node_zero D (f.leaf ⟨i,a⟩) (f.leaf ⟨i,firstLeaf (C i)⟩)).mpr h
  have hs := (splitDepth_same_child C i a (firstLeaf (C i))).symm.trans
    ((f.split ⟨i,a⟩ ⟨i,firstLeaf (C i)⟩).symm.trans hz)
  omega

lemma childIndex_injective (f : SplitMap (.node k C) (.node l D)) :
    Function.Injective f.childIndex := by
  intro i j hij
  by_contra h
  have hz : splitDepth (.node l D) (f.leaf ⟨i,firstLeaf (C i)⟩)
      (f.leaf ⟨j,firstLeaf (C j)⟩) = 0 := by
    exact (f.split ⟨i,firstLeaf (C i)⟩ ⟨j,firstLeaf (C j)⟩).trans
      (splitDepth_diff_child C i j h _ _)
  exact (splitDepth_node_zero D _ _).mp hz hij

def childLeaf (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    (D (f.childIndex i)).Leaf := f.rootAgreement i a ▸ (f.leaf ⟨i,a⟩).2

lemma leaf_eq_child (f : SplitMap (.node k C) (.node l D)) (i : Fin k) (a : (C i).Leaf) :
    f.leaf ⟨i,a⟩ = ⟨f.childIndex i,f.childLeaf i a⟩ := by
  have h := f.rootAgreement i a
  change f.leaf ⟨i,a⟩ = ⟨f.childIndex i,h ▸ (f.leaf ⟨i,a⟩).2⟩
  generalize f.leaf ⟨i,a⟩ = z at h ⊢
  obtain ⟨j,b⟩ := z
  dsimp at h ⊢
  subst j
  rfl

def child (f : SplitMap (.node k C) (.node l D)) (i : Fin k) :
    SplitMap (C i) (D (f.childIndex i)) where
  leaf := f.childLeaf i
  split a b := by
    have h := f.split ⟨i,a⟩ ⟨i,b⟩
    rw [f.leaf_eq_child i a,f.leaf_eq_child i b,splitDepth_same_child,splitDepth_same_child] at h
    omega

lemma arity_le (f : SplitMap (.node k C) (.node l D)) : (k:ℕ) ≤ l := by
  have h := Fintype.card_le_of_injective _ f.childIndex_injective
  simpa only [Fintype.card_fin] using h

/-- Exact split constraints force every target branching vertex to occur in
the actual history, even when several different vertices have equal depths. -/
theorem branchingCount_le {n : ℕ} {T S : PrescribedTree n} (f : SplitMap T S)
    (P : ℕ → Prop) : branchingCount T P ≤ branchingCount S P := by
  classical
  induction T generalizing P with
  | leaf => cases S; exact le_rfl
  | @node n k C ih =>
    cases S with
    | node l D =>
      change (if P 0 ∧ 1 < (k:ℕ) then 1 else 0) +
        (∑ i, branchingCount (C i) (fun d => P (d+1))) ≤
        (if P 0 ∧ 1 < (l:ℕ) then 1 else 0) +
        (∑ j, branchingCount (D j) (fun d => P (d+1)))
      apply Nat.add_le_add
      · split_ifs with hk hl hl
        · exact le_rfl
        · exact False.elim (hl ⟨hk.1,hk.2.trans_le f.arity_le⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · calc
          _ ≤ ∑ i, branchingCount (D (f.childIndex i)) (fun d => P (d+1)) :=
            Finset.sum_le_sum (fun i _ => ih i (f.child i) (fun d => P (d+1)))
          _ = ∑ j ∈ Finset.univ.image f.childIndex, branchingCount (D j) (fun d => P (d+1)) := by
            rw [Finset.sum_image]
            exact fun i _ j _ h => f.childIndex_injective h
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => Nat.zero_le _)

end SplitMap
end DilutedSpinGlass.PrescribedTree
end

end

end OAI
