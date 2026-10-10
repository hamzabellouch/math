import OAI.Combinatorics.ParityLifts.GlueVertices

namespace OAI

namespace ParityWL

open scoped BigOperators

section AddRoot

open scoped Classical

variable {N : Type} (D : RankedTree N)

noncomputable def addRootTree : RankedTree (Option N) where
  root := none
  parent := fun n => match n with
    | none => none
    | some a => if a = D.root then none else some (D.parent a)
  rank := fun n => match n with
    | none => 0
    | some a => D.rank a + 1
  parent_lt := by
    intro n hn
    cases n with
    | none => exact (hn rfl).elim
    | some a =>
      dsimp only
      split_ifs with ha
      · simp only; omega
      · exact Nat.add_lt_add_right (D.parent_lt a ha) 1

lemma addRoot_map_ancestor {a b : N} (h : D.Ancestor a b) :
    (addRootTree D).Ancestor (some a) (some b) := by
  apply RankedTree.Ancestor.map D (addRootTree D) some _ h
  intro j hj
  apply RankedTree.Ancestor.step (by simp [addRootTree])
  simp only [addRootTree, ite_eq_right hj]
  exact .refl

lemma addRoot_ancestor_some {a : N} {n : Option N}
    (h : (addRootTree D).Ancestor (some a) n) :
    ∃ b, n = some b ∧ D.Ancestor a b := by
  induction h with
  | refl => exact ⟨a, rfl, .refl⟩
  | @step n hn h ih =>
    cases n with
    | none => exact (hn rfl).elim
    | some b =>
      obtain ⟨c, hc, hac⟩ := ih
      change (if b = D.root then none else some (D.parent b)) = some c at hc
      by_cases hb : b = D.root
      · rw [ite_eq_left hb] at hc
        cases hc
      · rw [ite_eq_right hb] at hc
        exact ⟨b, rfl, .step hb (by rwa [Option.some.inj hc])⟩

lemma addRoot_ancestor_iff {a b : N} :
    (addRootTree D).Ancestor (some a) (some b) ↔ D.Ancestor a b := by
  constructor
  · intro h
    obtain ⟨c, hc, hac⟩ := addRoot_ancestor_some D h
    rwa [Option.some.inj hc]
  · exact addRoot_map_ancestor D

end AddRoot

section ReRoot

open scoped Classical

variable {r k t : ℕ} (F : RootedTest r t) (ρ : Fin k → Fin r)

def keepRoot (a : F.Vertex) := ∃ j, F.roots (ρ j) = a

noncomputable def reRootBag : Option F.Node → Finset F.Vertex
  | none => Finset.univ.image (F.roots ∘ ρ)
  | some n => F.tree.bag n

noncomputable def reRootTop (a : F.Vertex) : Option F.Node :=
  if keepRoot F ρ a then none else some (F.tree.top a)

lemma keep_top {a : F.Vertex} (ha : keepRoot F ρ a) : F.tree.top a = F.tree.root := by
  apply RankedTree.ancestor_root_eq
  apply F.tree.top_ancestor
  rw [F.root_bag]
  obtain ⟨j, hj⟩ := ha
  exact Finset.mem_image.mpr ⟨ρ j, Finset.mem_univ _, hj⟩

lemma reRootTop_mem (a : F.Vertex) : a ∈ reRootBag F ρ (reRootTop F ρ a) := by
  by_cases ha : keepRoot F ρ a
  · simp only [reRootTop, ite_eq_left ha, reRootBag, Finset.mem_image, Finset.mem_univ,
      true_and, Function.comp_apply]
    exact ha
  · simpa only [reRootTop, ite_eq_right ha, reRootBag] using F.tree.top_mem a

lemma reRootTop_ancestor (a : F.Vertex) (n : Option F.Node)
    (han : a ∈ reRootBag F ρ n) :
    (addRootTree F.tree.toRankedTree).Ancestor (reRootTop F ρ a) n := by
  by_cases ha : keepRoot F ρ a
  · rw [reRootTop, ite_eq_left ha]
    exact (addRootTree F.tree.toRankedTree).root_ancestor n
  · rw [reRootTop, ite_eq_right ha]
    cases n with
    | none => exact (ha (by simpa only [keepRoot, reRootBag, Finset.mem_image,
        Finset.mem_univ, true_and, Function.comp_apply] using han)).elim
    | some n => exact addRoot_map_ancestor _ (F.tree.top_ancestor a n han)

lemma reRootInterval_mem (a : F.Vertex) (n l : Option F.Node)
    (hn : (addRootTree F.tree.toRankedTree).Ancestor (reRootTop F ρ a) n)
    (hnl : (addRootTree F.tree.toRankedTree).Ancestor n l) (ha : a ∈ reRootBag F ρ l) :
    a ∈ reRootBag F ρ n := by
  cases n with
  | none =>
    have he := RankedTree.ancestor_root_eq (addRootTree F.tree.toRankedTree) hn
    have hk : keepRoot F ρ a := by
      by_contra hk
      rw [reRootTop, ite_eq_right hk] at he
      cases he
    simpa only [keepRoot, reRootBag, Finset.mem_image, Finset.mem_univ,
      true_and, Function.comp_apply] using hk
  | some n =>
    obtain ⟨l, rfl, hnl'⟩ := addRoot_ancestor_some _ hnl
    apply F.tree.interval_mem a n l _ hnl' ha
    by_cases hk : keepRoot F ρ a
    · rw [keep_top F ρ hk]
      exact F.tree.toRankedTree.root_ancestor n
    · rw [reRootTop, ite_eq_right hk] at hn
      exact (addRoot_ancestor_iff _).mp hn

noncomputable def reRootTest (hk : k < t) : RootedTest k t where
  Vertex := F.Vertex
  vertexFintype := F.vertexFintype
  relation := F.relation
  symmetric := F.symmetric
  roots := F.roots ∘ ρ
  Node := Option F.Node
  nodeFintype := inferInstance
  tree :=
    { toRankedTree := addRootTree F.tree.toRankedTree
      bag := reRootBag F ρ
      top := reRootTop F ρ
      top_mem := reRootTop_mem F ρ
      top_ancestor := reRootTop_ancestor F ρ
      interval_mem := reRootInterval_mem F ρ
      edge_cover := by
        intro a b hab
        obtain ⟨n, han, hbn⟩ := F.tree.edge_cover a b hab
        exact ⟨some n, han, hbn⟩
      width := by
        intro n
        cases n with
        | none =>
          exact le_trans Finset.card_image_le
            (by simpa only [Finset.card_univ, Fintype.card_fin] using hk.le)
        | some n => exact F.tree.width n
      intersection := by
        intro n hn
        cases n with
        | none => exact (hn rfl).elim
        | some n =>
          change (F.tree.bag n ∩ reRootBag F ρ
            (if n = F.tree.root then none else some (F.tree.parent n))).card < t
          by_cases he : n = F.tree.root
          · rw [ite_eq_left he]
            exact lt_of_le_of_lt ((Finset.card_le_card Finset.inter_subset_right).trans
              Finset.card_image_le) (by simpa using hk)
          · rw [ite_eq_right he]
            exact F.tree.intersection n he }
  root_bag := rfl

end ReRoot

section ForgetCount

open scoped Classical

variable {k t : ℕ} (F : RootedTest (k + 1) t) (i : Fin (k + 1)) (hk : k < t)
variable {V : Type} (G : SimpleGraph V) (x : Fin k → V)

noncomputable def reRootMapsEquiv :
    (reRootTest F i.succAbove hk).Maps G x ≃ ((y : V) × F.Maps G (i.insertNth y x)) where
  toFun f := ⟨f.1.1 (F.roots i), ⟨f.1, by
    intro j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp only [Fin.insertNth_apply_same]
    · rw [Fin.insertNth_apply_succAbove]
      exact f.2 l⟩⟩
  invFun f := ⟨f.2.1, by
    intro j
    change f.2.1.1 (F.roots (i.succAbove j)) = x j
    simpa only [Fin.insertNth_apply_succAbove] using f.2.2 (i.succAbove j)⟩
  left_inv _ := rfl
  right_inv f := by
    rcases f with ⟨y, f, hf⟩
    have hy : f.1 (F.roots i) = y := by
      simpa only [Fin.insertNth_apply_same] using hf i
    subst y
    rfl

lemma reRootTest_count [Fintype V] :
    (reRootTest F i.succAbove hk).count G x = ∑ y : V, F.count G (i.insertNth y x) := by
  unfold RootedTest.count
  rw [Fintype.card_congr (reRootMapsEquiv F i hk G x), Fintype.card_sigma, Nat.cast_sum]

end ForgetCount

end ParityWL

end OAI
