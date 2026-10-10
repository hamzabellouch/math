import OAI.Analysis.StrictMeans.CriticalCounts

namespace OAI

section
open Set

namespace StrictInverseFirstPower
noncomputable section

def descendingRank {X : Type*} (v : X → ℝ) (S : Set X) (x : X) : ℕ :=
  {y | y ∈ S ∧ v x < v y}.ncard

lemma descendingRank_lt_of_value_lt {X : Type*} {v : X → ℝ} {S : Set X}
    {x y : X} (hy : y ∈ S) (hxy : v x < v y)
    (hfin : {z | z ∈ S ∧ v x < v z}.Finite) :
    descendingRank v S y < descendingRank v S x := by
  unfold descendingRank
  apply Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩) hfin
  · intro z hz
    exact ⟨hz.1,hxy.trans hz.2⟩
  · intro he
    have hyx : y ∈ {z | z ∈ S ∧ v x < v z} := ⟨hy,hxy⟩
    rw [← he] at hyx
    exact lt_irrefl _ hyx.2

lemma descendingRank_injOn {X : Type*} {v : X → ℝ} {S : Set X}
    (hv : InjOn v S) (hfin : ∀ x ∈ S, {z | z ∈ S ∧ v x < v z}.Finite) :
    InjOn (descendingRank v S) S := by
  intro x hx y hy he
  apply hv hx hy
  rcases lt_trichotomy (v x) (v y) with hlt | heq | hgt
  · exact False.elim ((descendingRank_lt_of_value_lt hy hlt (hfin x hx)).ne he.symm)
  · exact heq
  · exact False.elim ((descendingRank_lt_of_value_lt hx hgt (hfin y hy)).ne he)

lemma exists_descendingRank_eq_of_finite {X : Type*} {v : X → ℝ} {S : Set X}
    (hS : S.Finite) (hv : InjOn v S) {n : ℕ} (hn : n < S.ncard) :
    ∃ x ∈ S, descendingRank v S x = n := by
  classical
  induction n generalizing S with
  | zero =>
    obtain ⟨m,hm,hmax⟩ := Set.exists_max_image S v hS (Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hn))
    refine ⟨m,hm,?_⟩
    unfold descendingRank
    have he : {y | y ∈ S ∧ v m < v y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact (hmax y hy.1).not_gt hy.2
    rw [he,Set.ncard_empty]
  | succ n ih =>
    obtain ⟨m,hm,hmax⟩ := Set.exists_max_image S v hS (Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hn)))
    let T := S \ {m}
    have hT : T.Finite := hS.sdiff
    have hnT : n < T.ncard := by
      have he : T.ncard + 1 = S.ncard := by
        simpa [T] using Set.ncard_sdiff_singleton_add_one hm hS
      omega
    obtain ⟨x,hx,hxrank⟩ := ih hT (hv.mono sdiff_subset) hnT
    have hxm : x ≠ m := by simpa only [T,mem_sdiff,mem_singleton_iff] using hx.2
    have hvxm : v x < v m := lt_of_le_of_ne (hmax x hx.1)
      (fun he => hxm (hv hx.1 hm he))
    have he : {y | y ∈ S ∧ v x < v y} = insert m {y | y ∈ T ∧ v x < v y} := by
      ext y
      simp only [mem_ofPred_eq,mem_insert_iff,T,mem_sdiff,mem_singleton_iff]
      constructor
      · intro hy
        by_cases hym : y = m
        · exact Or.inl hym
        · exact Or.inr ⟨⟨hy.1,hym⟩,hy.2⟩
      · rintro (rfl | hy)
        · exact ⟨hm,hvxm⟩
        · exact ⟨hy.1.1,hy.2⟩
    refine ⟨x,hx.1,?_⟩
    unfold descendingRank at hxrank ⊢
    rw [he,Set.ncard_insert_of_notMem (by simp [T]) (hT.subset (by intro y hy; exact hy.1)),hxrank]

lemma closedCut_ncard_eq_rank_succ {X : Type*} {v : X → ℝ} {S : Set X}
    (hv : InjOn v S) {x : X} (hx : x ∈ S)
    (hf : {y | y ∈ S ∧ v x ≤ v y}.Finite) :
    {y | y ∈ S ∧ v x ≤ v y}.ncard = descendingRank v S x + 1 := by
  classical
  have he : {y | y ∈ S ∧ v x ≤ v y} = insert x {y | y ∈ S ∧ v x < v y} := by
    ext y
    simp only [mem_ofPred_eq,mem_insert_iff]
    constructor
    · intro hy
      rcases eq_or_lt_of_le hy.2 with h | h
      · exact Or.inl (hv hy.1 hx h.symm)
      · exact Or.inr ⟨hy.1,h⟩
    · rintro (rfl | hy)
      · exact ⟨hx,le_rfl⟩
      · exact ⟨hy.1,hy.2.le⟩
  unfold descendingRank
  rw [he,Set.ncard_insert_of_notMem (by simp) (hf.subset (by intro y hy; exact ⟨hy.1,hy.2.le⟩))]

lemma descendingRank_closedCut {X : Type*} (v : X → ℝ) (S : Set X)
    {h : ℝ} {x : X} (hx : h ≤ v x) :
    descendingRank v {y | y ∈ S ∧ h ≤ v y} x = descendingRank v S x := by
  unfold descendingRank
  congr 1
  ext y
  constructor
  · intro hh
    exact ⟨hh.1.1,hh.2⟩
  · intro hh
    exact ⟨⟨hh.1,hx.trans hh.2.le⟩,hh.2⟩

lemma higher_partner_of_cut_domination {X : Type*} {v : X → ℝ} {A B : Set X}
    (hdisj : Disjoint A B) (hv : InjOn v (A ∪ B)) {a : X} (ha : a ∈ A)
    (hfA : {y | y ∈ A ∧ v a ≤ v y}.Finite)
    (hfB : {y | y ∈ B ∧ v a ≤ v y}.Finite)
    (hcount : {y | y ∈ A ∧ v a ≤ v y}.ncard ≤ {y | y ∈ B ∧ v a ≤ v y}.ncard) :
    ∃ b ∈ B, v a < v b ∧ descendingRank v B b = descendingRank v A a := by
  have hrank : descendingRank v A a < {y | y ∈ B ∧ v a ≤ v y}.ncard := by
    rw [closedCut_ncard_eq_rank_succ (hv.mono subset_union_left) ha hfA] at hcount
    omega
  obtain ⟨b,hb,hr⟩ := exists_descendingRank_eq_of_finite hfB
    (hv.mono (by intro x hx; exact Or.inr hx.1)) hrank
  refine ⟨b,hb.1,?_,?_⟩
  · apply lt_of_le_of_ne hb.2
    intro he
    have hab := hv (Or.inl ha) (Or.inr hb.1) he
    exact Set.disjoint_left.mp hdisj (hab ▸ ha) hb.1
  · rwa [descendingRank_closedCut v B hb.2] at hr

end
end StrictInverseFirstPower

end

end OAI
