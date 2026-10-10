import OAI.Analysis.DiamondDistortion.DirectEnergy

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

open scoped ENNReal

namespace LpCut
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
def linear (H : ι → Prop) [DecidablePred H] : lp (fun _ : ι => ℝ) p →ₗ[ℝ] lp (fun _ : ι => ℝ) p where
  toFun v := ⟨fun i => if H i then v i else 0,v.property.mono' (fun i => by split_ifs <;> simp)⟩
  map_add' u v := by
    ext i
    change (if H i then u i+v i else 0)=(if H i then u i else 0)+(if H i then v i else 0)
    by_cases h : H i <;> simp [h]
  map_smul' c v := by ext i; by_cases h : H i <;> simp [h]
lemma linear_apply {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (H : ι → Prop) [DecidablePred H] (v : lp (fun _ : ι => ℝ) p) (i : ι) :
    linear H v i=if H i then v i else 0 := rfl
lemma norm_linear (H : ι → Prop) [DecidablePred H] (v : lp (fun _ : ι => ℝ) p) : ‖linear H v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
  intro i
  rw [linear_apply]
  split_ifs <;> simp
def continuous (H : ι → Prop) [DecidablePred H] : lp (fun _ : ι => ℝ) p →L[ℝ] lp (fun _ : ι => ℝ) p :=
  (linear H).mkContinuous 1 (fun v => by simpa only [one_mul] using norm_linear H v)
lemma continuous_apply (H : ι → Prop) [DecidablePred H] (v : lp (fun _ : ι => ℝ) p) (i : ι) :
    continuous H v i=if H i then v i else 0 := rfl
end LpCut

namespace RecursiveModel
lemma ancestors_linear (h : ℕ) {a b c : Coord h}
    (ha : a ∈ ancestors h c) (hb : b ∈ ancestors h c) :
    a ∈ ancestors h b ∨ b ∈ ancestors h a := by
  induction h with
  | zero => left; exact self_mem_ancestors _ _
  | succ h ih =>
    cases c with
    | inl u =>
      have hak : a=Sum.inl () := by simpa only [ancestors,Finset.mem_singleton] using ha
      have hbk : b=Sum.inl () := by simpa only [ancestors,Finset.mem_singleton] using hb
      subst a; subst b
      exact Or.inl (self_mem_ancestors _ _)
    | inr q =>
      rcases Finset.mem_insert.mp ha with ha|ha
      · subst a
        rcases Finset.mem_insert.mp hb with hb|hb
        · subst b; exact Or.inl (self_mem_ancestors _ _)
        · obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
          exact Or.inl (Finset.mem_insert_self _ _)
      · obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
        rcases Finset.mem_insert.mp hb with hb|hb
        · subst b; exact Or.inr (Finset.mem_insert_self _ _)
        · obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
          rcases ih ha' hb' with h|h
          · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a',h,rfl⟩))
          · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b',h,rfl⟩))

lemma ancestral_prefix (h : ℕ) (H : Coord h → Prop) [DecidablePred H]
    (hH : ∀ a b,H b → a ∈ ancestors h b → H a) (s : Coord h) :
    (ancestors h s).filter H=∅ ∨ ∃ t,(ancestors h s).filter H=ancestors h t := by
  let S := (ancestors h s).filter H
  by_cases hn : S.Nonempty
  · obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image S (fun t => (ancestors h t).card) hn
    refine Or.inr ⟨t,?_⟩
    apply Finset.Subset.antisymm
    · intro r hr
      have hrs := (Finset.mem_filter.mp hr).1
      have hts := (Finset.mem_filter.mp ht).1
      rcases ancestors_linear h hrs hts with he|he
      · exact he
      · have hs : ancestors h t ⊆ ancestors h r := fun _ hk => ancestor_trans h hk he
        have hc := hmax r hr
        have heq := Finset.eq_of_subset_of_card_le hs hc
        rw [heq]
        exact self_mem_ancestors h r
    · intro r hr
      exact Finset.mem_filter.mpr ⟨ancestor_trans h hr (Finset.mem_filter.mp ht).1,
        hH r t (Finset.mem_filter.mp ht).2 hr⟩
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)
end RecursiveModel

namespace PathModel
open RecursiveModel
lemma cut_branch (h : ℕ) (H : Coord h → Prop) [DecidablePred H]
    (hH : ∀ a b,H b → a ∈ ancestors h b → H a) (s : Coord h) :
    LpCut.continuous H (branch h s)=0 ∨ ∃ t,LpCut.continuous H (branch h s)=branch h t := by
  rcases ancestral_prefix h H hH s with he|⟨t,he⟩
  · left
    ext r
    rw [LpCut.continuous_apply,branch_apply]
    by_cases hr : H r
    · rw [ite_eq_left hr,ite_eq_right (by
        intro hh
        have hk := Finset.mem_filter.mpr ⟨hh,hr⟩
        rw [he] at hk
        exact Finset.notMem_empty r hk)]
      rfl
    · rw [ite_eq_right hr]; rfl
  · right
    refine ⟨t,?_⟩
    ext r
    rw [LpCut.continuous_apply,branch_apply,branch_apply]
    have hm : r ∈ ancestors h t ↔ r ∈ ancestors h s ∧ H r := by rw [← he,Finset.mem_filter]
    by_cases h₁ : H r <;> by_cases h₂ : r ∈ ancestors h s <;> simp [h₁,h₂,hm]

lemma branch_cost (h : ℕ) (s : Coord h) : cost 1 h (branch h s) ≤ 1 := by
  have hh := (presentation 1 h).le_representation (d := WithLp.toLp 1 ((0 : L2 h),lp.single 1 s (1:ℝ)))
    (show (presentation 1 h).output (WithLp.toLp 1 (0,lp.single 1 s (1:ℝ)))=branch h s by
      change 0+path h (lp.single 1 s 1)=_
      rw [zero_add,path_single,one_smul])
  simpa only [WithLp.prod_norm_eq_of_L1,WithLp.fst,WithLp.snd,WithLp.ofLp_toLp,norm_zero,zero_add,
    lp.norm_single (by norm_num : (0:ℝ≥0∞)<1),norm_one,cost] using hh

lemma linear_cost_cut (h : ℕ) (H : Coord h → Prop) [DecidablePred H]
    (hH : ∀ a b,H b → a ∈ ancestors h b → H a) (v : L2 h) :
    cost 1 h (LpCut.continuous H v) ≤ cost 1 h v := by
  let E := linearFullData h
  let T : L2 h →L[ℝ] E.Space := E.equiv.symm.toContinuousLinearMap.comp (LpCut.continuous H)
  have hbranch (s : Coord h) : ‖T (branch h s)‖ ≤ 1 := by
    change cost 1 h (LpCut.continuous H (branch h s)) ≤ 1
    rcases cut_branch h H hH s with he|⟨t,he⟩
    · rw [he,map_zero]; norm_num
    · rw [he]; exact branch_cost h t
  have hp (μ : L1 h) : cost 1 h (LpCut.continuous H (path h μ)) ≤ ‖μ‖ := by
    have hnorm : Summable (fun s => ‖μ s • T (branch h s)‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable_abs μ)
      intro s
      rw [norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hbranch s) (abs_nonneg _)).trans_eq (mul_one _)
    have hsum := (path_summable μ).hasSum.mapL T
    simp_rw [map_smul] at hsum
    change ‖T (path h μ)‖ ≤ ‖μ‖
    change ‖T (∑' s,μ s • branch h s)‖ ≤ ‖μ‖
    rw [← hsum.tsum_eq]
    calc
      _ ≤ ∑' s,‖μ s • T (branch h s)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' s,|μ s| := Summable.tsum_le_tsum (fun s => by
        rw [norm_smul,Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hbranch s) (abs_nonneg _)).trans_eq (mul_one _)) hnorm (summable_abs μ)
      _ = ‖μ‖ := tsum_abs μ
  have hb := (presentation 1 h).bound v (by norm_num : (0:ℝ) ≤ 1) (b := cost 1 h (LpCut.continuous H v))
  simp only [one_mul] at hb
  apply hb
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd,map_add,WithLp.prod_norm_eq_of_L1]
  exact (map_add_le_add (cost 1 h) _ _).trans (add_le_add
    ((linear_le_norm _ _).trans (LpCut.norm_linear _ _)) (hp d.snd))
end PathModel

namespace CoordinateCompletion.Data
variable {ι : Type*} (A : CoordinateCompletion.Data ι)
lemma projection_nested (H B : Finset ι) (hHB : H ⊆ B) (x : A.Space) :
    A.projection H (A.projection B x)=A.projection H x := by
  rw [A.projection_apply H (A.projection B x)]
  simp only [coordinate_projection]
  rw [A.projection_apply H x]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ite_eq_left (hHB hi)]
lemma projection_nested_right (H B : Finset ι) (hHB : H ⊆ B) (x : A.Space) :
    A.projection B (A.projection H x)=A.projection H x := by
  rw [A.projection_commutes B H]
  exact A.projection_nested H B hHB x
end CoordinateCompletion.Data

namespace RecursiveModel
instance : PartialOrder ForestHead := inferInstanceAs (PartialOrder {H : Finset ForestCoord // ∀ i ∈ H,forestAncestors i ⊆ H})
lemma head_upper (H K : ForestHead) : ∃ B : ForestHead,H ≤ B ∧ K ≤ B := by
  let B : ForestHead := ⟨H.val ∪ K.val,by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ (H.property i hi hj)
    · exact Finset.mem_union_right _ (K.property i hi hj)⟩
  exact ⟨B,Finset.subset_union_left,Finset.subset_union_right⟩
lemma head_nonempty : Nonempty ForestHead := ⟨forestHead ∅⟩
end RecursiveModel

namespace PathModel
open RecursiveModel
lemma linear_forest_cut (v : ForestVec) (H : ForestHead) :
    linearForestSeminorm (v.filter (· ∈ H.val)) ≤ linearForestSeminorm v := by
  apply aggregate_mono 2
  · exact outerValues_nonneg _ _
  · intro h
    rw [outerValues_apply,outerValues_apply]
    change cost 1 (h+1) (finiteEmbedding _ (components (v.filter (· ∈ H.val)) h)) ≤
      cost 1 (h+1) (finiteEmbedding _ (components v h))
    have he : finiteEmbedding (h+1) (components (v.filter (· ∈ H.val)) h)=
        LpCut.continuous (fun i : Coord (h+1) => (⟨h,i⟩ : ForestCoord) ∈ H.val)
          (finiteEmbedding (h+1) (components v h)) := by
      ext i
      change (v.filter (· ∈ H.val)) ⟨h,i⟩=if (⟨h,i⟩ : ForestCoord) ∈ H.val then v ⟨h,i⟩ else 0
      exact Finsupp.filter_apply _ _ _
    rw [he]
    apply linear_cost_cut
    intro a b hb hab
    exact H.property ⟨h,b⟩ hb (Finset.mem_image.mpr ⟨a,hab,rfl⟩)
lemma linear_projection_contractive (H : ForestHead) (x : linearData.Space) :
    ‖linearData.projection H.val x‖ ≤ ‖x‖ := by
  rcases H with ⟨H,hH⟩
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih v =>
    change ‖linearData.projection H (linearData.embedding (linearData.array v))‖ ≤ ‖linearData.embedding (linearData.array v)‖
    rw [linearData.projection_embedding,linearData.norm_embedding,linearData.norm_embedding]
    convert linear_forest_cut (linearData.array v) ⟨H,hH⟩ using 1 <;> congr 1
    ext i
    simp only [Finsupp.filter_apply]
    by_cases hi : i ∈ H <;> simp only [hi,ite_eq_left]
end PathModel

end DiamondDistortion

end

end OAI
