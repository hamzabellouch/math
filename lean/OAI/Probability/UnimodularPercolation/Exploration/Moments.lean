import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.Marked

namespace OAI

/-! Recursive marked moments and exponential estimates. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section OrderedPivotalMoments
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem sum_choose_rank_suffix {I : Type*} (P : Finset I) (rank : I → ℕ)
    (hinj : Set.InjOn rank (P : Set I)) (i : ℕ) :
    (∑ e ∈ P, ((P.filter fun f => rank e < rank f).card).choose i) =
      P.card.choose (i+1) := by
  induction P using Finset.strongInductionOn with
  | _ P ih =>
    rcases P.eq_empty_or_nonempty with rfl | hP
    · simp
    obtain ⟨e,he,hmin⟩ := Finset.exists_min_image P rank hP
    have hT : P.erase e ⊂ P := Finset.erase_ssubset he
    have hinjT : Set.InjOn rank (↑(P.erase e) : Set I) := fun a ha b hb =>
      hinj (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)
    have hroot : P.filter (fun f => rank e < rank f) = P.erase e := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hf,hlt⟩
        exact ⟨fun h => (Nat.ne_of_lt hlt) (congrArg rank h.symm),hf⟩
      · rintro ⟨hne,hf⟩
        exact ⟨hf,lt_of_le_of_ne (hmin f hf) (fun h => hne (hinj he hf h).symm)⟩
    have hrest (f : I) (hf : f ∈ P.erase e) :
        P.filter (fun g => rank f < rank g) = (P.erase e).filter (fun g => rank f < rank g) := by
      ext g
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨hg,hfg⟩
        refine ⟨⟨?_,hg⟩,hfg⟩
        intro h; subst g
        exact (not_lt_of_ge (hmin f (Finset.mem_of_mem_erase hf))) hfg
      · exact fun h => ⟨h.1.2,h.2⟩
    calc
      _ = (∑ f ∈ P.erase e, ((P.filter fun g => rank f < rank g).card).choose i) +
          ((P.filter fun f => rank e < rank f).card).choose i :=
        (Finset.sum_erase_add _ _ he).symm
      _ = (∑ f ∈ P.erase e, (((P.erase e).filter fun g => rank f < rank g).card).choose i) +
          (P.erase e).card.choose i := by
        rw [hroot]
        congr 1
        exact Finset.sum_congr rfl fun f hf => congrArg (fun s : Finset I => s.card.choose i) (hrest f hf)
      _ = (P.erase e).card.choose (i+1)+(P.erase e).card.choose i := by rw [ih _ hT hinjT]
      _ = P.card.choose (i+1) := by
        have hc : (P.erase e).card+1=P.card := by
          rw [Finset.card_erase_of_mem he]
          have hp := Finset.card_pos.mpr hP
          omega
        rw [← hc,Nat.choose_succ_succ]
        simp [Nat.succ_eq_add_one,Nat.add_comm]

end OrderedPivotalMoments

section MarkedRecursion
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem cluster_union_external (G : BondGraph V E) (ω η : Set E) (x : V) (W : Set V)
    (hω : cluster G ω x ⊆ W) (hη : η ⊆ internalEdges G Wᶜ) :
    cluster G (ω ∪ η) x = cluster G ω x := by
  apply Set.Subset.antisymm
  · intro y hy
    induction hy with
    | refl => exact conn_refl G ω x
    | @tail a b hxa hab ih =>
      obtain ⟨e,he,heq⟩ := hab
      rcases he with he | he
      · exact ih.tail ⟨e,he,heq⟩
      · exact (((mem_internalEdges_of_ends G _ e a b heq).mp (hη he)).1 (hω ih)).elim
  · exact fun _ h => conn_mono G Set.subset_union_left h

 
theorem cluster_union_external_eq_iff (G : BondGraph V E) (ω η : Set E)
    (x : V) (W : Set V) (hη : η ⊆ internalEdges G Wᶜ) :
    cluster G (ω ∪ η) x = W ↔ cluster G ω x = W := by
  constructor
  · intro h
    have hω : cluster G ω x ⊆ W := fun y hy => h ▸ conn_mono G Set.subset_union_left hy
    rwa [cluster_union_external G ω η x W hω hη] at h
  · intro h
    rw [cluster_union_external G ω η x W (h ▸ Set.Subset.rfl) hη,h]

 
theorem markedEvent_internal_marks (G : BondGraph V E) (ω : Set E) (m W : Set V)
    (x : V) (hx : x ∈ W) (hω : ω ⊆ internalEdges G W) :
    MarkedEvent G ω m x ↔ MarkedEvent G ω (m ∩ W) x := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,⟨hy,conn_internal_endpoint G W hx (conn_mono G
      (ω₁ := ω) (ω₂ := ω ∩ internalEdges G W) (fun _ h => ⟨h,hω h⟩) hxy)⟩,hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,hy.1,hxy⟩

theorem openMarkedPivotal_internal_marks (G : BondGraph V E) (ω : Set E)
    (m W : Set V) (x : V) (hx : x ∈ W) (hω : ω ⊆ internalEdges G W) (e : E) :
    OpenMarkedPivotal G ω m x e ↔ OpenMarkedPivotal G ω (m ∩ W) x e := by
  simp only [OpenMarkedPivotal,markedEvent_internal_marks G ω m W x hx hω,
    markedEvent_internal_marks G (ω \ {e}) m W x hx (Set.Subset.trans Set.sdiff_subset hω)]

 
theorem openMarkedPivotal_insert_cut (G : BondGraph V E) (ω : Set E) (m W : Set V)
    (x : V) {e : E} {a b : V} (hW : cluster G ω x = W)
    (hab : G e = s(a,b)) (ha : a ∈ W) (hb : b ∉ W) :
    OpenMarkedPivotal G (insert e ω) m x e ↔
      Disjoint W m ∧ MarkedEvent G (ω ∩ internalEdges G Wᶜ) (m ∩ Wᶜ) b := by
  have he : e ∉ ω := fun he => hb (hW ▸ ((edge_cluster_sides G ω x he hab).mp (hW ▸ ha)))
  have hdel : insert e ω \ {e} = ω := by ext f; simp [he]
  have hxa : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hW]
  constructor
  · intro hp
    have hdis := pivotal_rootSide_disjoint_marks G (insert e ω) m x hp
    rw [hdel,hW] at hdis
    refine ⟨hdis,?_⟩
    obtain ⟨y,hy,hxy⟩ := hp.2.1
    rw [conn_insert_iff G ω e a b x y hab] at hxy
    rcases hxy with hxy | ⟨_,hby⟩ | ⟨hxb,_⟩
    · exact (Set.disjoint_left.mp hdis (hW ▸ hxy) hy).elim
    · have hby' := conn_restrict_cluster_compl G ω x (a := b) (hW ▸ hb) hby
      rw [hW] at hby'
      exact (markedEvent_internal_marks G _ m Wᶜ b hb Set.inter_subset_right).mp ⟨y,hy,hby'⟩
    · exact (hb (hW ▸ hxb)).elim
  · rintro ⟨hdis,y,hy,hby⟩
    refine ⟨Set.mem_insert _ _,?_,?_⟩
    · exact ⟨y,hy.1,(conn_mono G (Set.subset_insert e ω) hxa).tail
        ⟨e,Set.mem_insert _ _,hab⟩ |>.trans (conn_mono G
          (fun _ h => Set.mem_insert_of_mem _ h.1) hby)⟩
    · rw [hdel]
      rintro ⟨z,hz,hxz⟩
      exact Set.disjoint_left.mp hdis (hW ▸ hxz) hz

@[simp] theorem mem_markedOpenPivotals (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) (e : E) :
    e ∈ markedOpenPivotals G Q x ω m ↔ e ∈ Q ∧ OpenMarkedPivotal G ω m x e := by
  simp only [markedOpenPivotals,Finset.mem_filter,OpenMarkedPivotal,MarkedEvent,Finset.coe_erase,
    Finset.mem_coe]

 
noncomputable def markedMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if MarkedEvent G ω m x then ((markedOpenPivotals G Q x ω m).card.choose i : ℝ) else 0

 
theorem markedMomentValue_succ (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x (i+1) ω m =
      ∑ e ∈ markedOpenPivotals G Q x ω m,
        (((markedOpenPivotals G Q x ω m).filter
          (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)).card.choose i : ℝ) := by
  have hinj : Set.InjOn (pivotalRank G ω x) (↑(markedOpenPivotals G Q x ω m) : Set E) := by
    intro e he f hf
    exact pivotalRank_injective G ω.finite_toSet m x
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2
      ((mem_markedOpenPivotals G Q x ω m f).mp hf).2
  have hs := sum_choose_rank_suffix (markedOpenPivotals G Q x ω m) (pivotalRank G ω x) hinj i
  have heq (e : E) (he : e ∈ markedOpenPivotals G Q x ω m) :
      (markedOpenPivotals G Q x ω m).filter (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) =
      (markedOpenPivotals G Q x ω m).filter (fun f => pivotalRank G ω x e < pivotalRank G ω x f) := by
    apply Finset.filter_congr
    intro f hf
    exact (pivotalRank_lt_iff G ω.finite_toSet m x
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2
      ((mem_markedOpenPivotals G Q x ω m f).mp hf).2).symm
  by_cases h : MarkedEvent G ω m x
  · simp only [markedMomentValue,h,ite_true]
    rw [← hs,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [heq e he]
  · have hempty : markedOpenPivotals G Q x ω m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h ((mem_markedOpenPivotals G Q x ω m e).mp he).2.2.1
    simp [markedMomentValue,h,hempty]

 
theorem conn_mem_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) {y : V} (hxy : Conn G ω x y) :
    y ∈ insert x (searchVertices G Q) := by
  induction hxy with
  | refl => exact Finset.mem_insert_self _ _
  | @tail a b hxa hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact Finset.mem_insert_of_mem (mem_searchVertices G (hω he) (by simp [heq]))

theorem markedEvent_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    {ω : Set E} (hω : ω ⊆ Q) (m : Set V) :
    MarkedEvent G ω m x ↔ MarkedEvent G ω (m ∩ ↑(insert x (searchVertices G Q))) x := by
  constructor
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,⟨hy,conn_mem_searchSupport G Q x hω hxy⟩,hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨y,hy.1,hxy⟩

theorem markedOpenPivotals_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    markedOpenPivotals G Q x ω m =
      markedOpenPivotals G Q x ω (m ∩ insert x (searchVertices G Q)) := by
  ext e
  simp only [mem_markedOpenPivotals,OpenMarkedPivotal,Finset.coe_inter]
  rw [markedEvent_searchSupport G Q x (by exact_mod_cast hω),
    markedEvent_searchSupport G Q x (ω := (ω : Set E) \ {e})
      (fun _ h => hω h.1)]

theorem markedMomentValue_searchSupport (G : BondGraph V E) (Q : Finset E) (x : V)
    (i : ℕ) (ω : Finset E) (hω : ω ⊆ Q) (m : Finset V) :
    markedMomentValue G Q x i ω m =
      markedMomentValue G Q x i ω (m ∩ insert x (searchVertices G Q)) := by
  unfold markedMomentValue
  rw [markedOpenPivotals_searchSupport G Q x ω hω m]
  simp only [Finset.coe_inter]
  rw [markedEvent_searchSupport G Q x (by exact_mod_cast hω)]

@[simp] theorem markedMomentValue_zero (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 0 ω m = if MarkedEvent G ω m x then 1 else 0 := by
  simp only [markedMomentValue,Nat.choose_zero_right,Nat.cast_one]

@[simp] theorem markedMomentValue_one (G : BondGraph V E) (Q : Finset E) (x : V)
    (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x 1 ω m = ((markedOpenPivotals G Q x ω m).card : ℝ) := by
  by_cases h : MarkedEvent G ω m x
  · simp [markedMomentValue,h]
  · have he : markedOpenPivotals G Q x ω m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h ((mem_markedOpenPivotals G Q x ω m e).mp he).2.2.1
    simp [markedMomentValue,h,he]

 
noncomputable def finiteMarkedMoment (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (markedMomentValue G Q x i ω) h) p

theorem finiteMarkedMoment_support (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x i h p =
      finiteMarkedMoment G Q (insert x (searchVertices G Q)) x i h p := by
  apply bernoulliPolynomial_congr
  intro ω hω
  rw [← bernoulliPolynomial_restrict _ F hF]
  apply bernoulliPolynomial_congr
  intro m _
  exact markedMomentValue_searchSupport G Q x i ω hω m

 
theorem finiteMarkedMoment_first_bound (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (p h : unitInterval) (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x 1 h p ≤
      (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)*
        finiteMarkedMoment G Q F x 0 h p := by
  rw [finiteMarkedMoment_support G Q F x 1 h p hF,
    finiteMarkedMoment_support G Q F x 0 h p hF]
  simpa only [finiteMarkedMoment,markedMomentValue_one,markedMomentValue_zero,MarkedEvent,
    markedPivotalMomentOne,markedConnectionPolynomial,bernoulliPolynomial,Finset.mem_coe] using
    marked_pivotal_first_moment G Q x p h hp hh d hd hdeg

noncomputable def exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) : Finset E :=
  Q.filter fun e => e ∈ internalEdges G Wᶜ

noncomputable def exteriorMarks (m : Finset V) (W : Set V) : Finset V :=
  m.filter fun x => x ∉ W

@[simp] theorem coe_exteriorBonds (G : BondGraph V E) (Q : Finset E) (W : Set V) :
    (exteriorBonds G Q W : Set E) = (Q : Set E) ∩ internalEdges G Wᶜ := by
  ext e; simp [exteriorBonds]

@[simp] theorem coe_exteriorMarks (m : Finset V) (W : Set V) :
    (exteriorMarks m W : Set V) = (m : Set V) ∩ Wᶜ := by
  ext x; simp [exteriorMarks]

 
theorem markedOpenPivotals_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (ω : Finset E) (m : Finset V) {e : E}
    (he : OpenMarkedPivotal G ω m x e) :
    markedOpenPivotals G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e)
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) =
      (markedOpenPivotals G Q x ω m).filter
        (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) := by
  obtain ⟨a,b,hab,hxa,hxb,hbm⟩ := openMarkedPivotal_oriented G ω m x he
  have hb := (cut_unique G (cluster G (↑ω \ {e}) x) hab hxa hxb).2
  rw [← hb]
  ext f
  simp only [mem_markedOpenPivotals,exteriorBonds,Finset.mem_filter,coe_exteriorMarks,
    Finset.coe_filter]
  have hmarks := openMarkedPivotal_internal_marks G
    ((ω : Set E) ∩ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)
    m (cluster G (↑ω \ {e}) x)ᶜ b hxb Set.inter_subset_right f
  have hiff := openMarkedPivotal_exterior_iff G ω m x he hab hxa hxb hbm f
  change (f ∈ Q ∧ f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ) ∧
    OpenMarkedPivotal G ((ω : Set E) ∩ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)
      ((m : Set V) ∩ (cluster G (↑ω \ {e}) x)ᶜ) b f ↔ _
  rw [← hmarks,hiff]
  tauto

 
theorem markedMomentValue_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (i : ℕ) (ω : Finset E) (m : Finset V) {e : E}
    (he : OpenMarkedPivotal G ω m x e) :
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) =
      (((markedOpenPivotals G Q x ω m).filter
        (fun f => f ∈ internalEdges G (cluster G (↑ω \ {e}) x)ᶜ)).card.choose i : ℝ) := by
  have hsuccess : MarkedEvent G (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) := by
    obtain ⟨a,b,hab,hxa,hxb,y,hy,hby⟩ := openMarkedPivotal_oriented G ω m x he
    rw [← (cut_unique G (cluster G (↑ω \ {e}) x) hab hxa hxb).2,
      coe_exteriorBonds,coe_exteriorMarks]
    apply (markedEvent_internal_marks G _ m (cluster G (↑ω \ {e}) x)ᶜ b hxb
      Set.inter_subset_right).mp
    refine ⟨y,hy,conn_mono G ?_ (conn_restrict_cluster_compl G (↑ω \ {e}) x hxb hby)⟩
    exact fun _ h => ⟨h.1.1,h.2⟩
  rw [markedMomentValue,ite_eq_left hsuccess,markedOpenPivotals_exterior G Q x ω m he]

 
theorem markedMomentValue_succ_exterior [Nonempty V] (G : BondGraph V E) (Q : Finset E)
    (x : V) (i : ℕ) (ω : Finset E) (m : Finset V) :
    markedMomentValue G Q x (i+1) ω m = ∑ e ∈ Q,
      if OpenMarkedPivotal G ω m x e then
        markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
          (cutOutside G (cluster G (↑ω \ {e}) x) e) i
          (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
          (exteriorMarks m (cluster G (↑ω \ {e}) x)) else 0 := by
  rw [markedMomentValue_succ]
  trans ∑ e ∈ markedOpenPivotals G Q x ω m,
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x))
  · apply Finset.sum_congr rfl
    intro e he
    exact (markedMomentValue_exterior G Q x i ω m
      ((mem_markedOpenPivotals G Q x ω m e).mp he).2).symm
  · have heq : markedOpenPivotals G Q x ω m = Q.filter (fun e => OpenMarkedPivotal G ω m x e) := by
      ext e; simp only [mem_markedOpenPivotals,Finset.mem_filter]
    rw [heq,Finset.sum_filter]

end MarkedRecursion

section CutFactor
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def cutMomentValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if cluster G ω x = (W : Set V) then
    if Disjoint (W : Set V) (m : Set V) then
      markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i
        (exteriorBonds G ω W) (exteriorMarks m W)
    else 0
  else 0

omit [Nonempty V] in
theorem cut_not_exterior (G : BondGraph V E) (W : Set V) {e : E}
    (hc : CutExists G W e) : e ∉ internalEdges G Wᶜ := by
  obtain ⟨a,b,hab,ha,hb⟩ := hc
  intro he
  exact ((mem_internalEdges_of_ends G Wᶜ e a b hab).mp he).1 ha

omit [Nonempty V] in
theorem exteriorBonds_subset_erase (G : BondGraph V E) (Q : Finset E)
    (W : Set V) {e : E} (hc : CutExists G W e) : exteriorBonds G Q W ⊆ Q.erase e := by
  intro f hf
  obtain ⟨hf,hout⟩ := Finset.mem_filter.mp hf
  exact Finset.mem_erase.mpr ⟨fun h => cut_not_exterior G W hc (h ▸ hout),hf⟩

 
theorem cutMomentValue_blocks (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (i : ℕ) (a b : Finset E) (u v : Finset V)
    (ha : a ⊆ (Q.erase e) \ exteriorBonds G Q W)
    (hb : b ⊆ exteriorBonds G Q W) (hu : u ⊆ W) (hv : v ⊆ F \ W) :
    cutMomentValue G Q x e W i (a ∪ b) (u ∪ v) =
      (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
      (if u = ∅ then (1:ℝ) else 0) *
      markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i b v := by
  have hbout : (b : Set E) ⊆ internalEdges G (W : Set V)ᶜ :=
    fun f hf => (Finset.mem_filter.mp (hb hf)).2
  have hc := cluster_union_external_eq_iff G (a : Set E) b x W hbout
  have he : exteriorBonds G (a ∪ b) W = b := by
    ext f
    simp only [exteriorBonds,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hf,hout⟩
      rcases hf with hf | hf
      · have hfa := Finset.mem_sdiff.mp (ha hf)
        exact (hfa.2 (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hfa.1,hout⟩)).elim
      · exact hf
    · exact fun hf => ⟨Or.inr hf,hbout hf⟩
  have hm : exteriorMarks (u ∪ v) W = v := by
    ext y
    simp only [exteriorMarks,Finset.mem_filter,Finset.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨hy,hyW⟩
      rcases hy with hy | hy
      · exact (hyW (hu hy)).elim
      · exact hy
    · intro hy
      exact ⟨Or.inr hy,(Finset.mem_sdiff.mp (hv hy)).2⟩
  have hd : Disjoint (W : Set V) ((u ∪ v : Finset V) : Set V) ↔ u = ∅ := by
    constructor
    · intro h
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact Set.disjoint_left.mp h (hu hy) (Finset.mem_union_left v hy)
    · rintro rfl
      apply Set.disjoint_left.mpr
      intro y hy hyv
      have hyv' : y ∈ v := by simpa using hyv
      exact (Finset.mem_sdiff.mp (hv hyv')).2 hy
  rw [Finset.coe_union] at hd
  simp only [cutMomentValue,Finset.coe_union,hc,hd,he,hm]
  split_ifs <;> simp_all

omit [Nonempty V] in
 
theorem bernoulliPolynomial_empty_indicator (F : Finset V) (h : ℝ) :
    bernoulliPolynomial F (fun m => if m = ∅ then (1:ℝ) else 0) h = (1-h)^F.card := by
  unfold bernoulliPolynomial
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro m hm hne
    simp [hne]
  · simp

 
theorem cutMoment_factor (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (i : ℕ) (h p : ℝ) (hW : W ⊆ F) (hc : CutExists G W e) :
    bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
      (cutMomentValue G Q x e W i ω) h) p =
      bernoulliPolynomial ((Q.erase e) \ exteriorBonds G Q W)
        (fun a => if cluster G a x = (W : Set V) then (1:ℝ) else 0) p *
      (1-h)^W.card * finiteMarkedMoment G (exteriorBonds G Q W) (F \ W)
        (cutOutside G W e) i h p := by
  let R := exteriorBonds G Q W
  let A := (Q.erase e) \ R
  let B := F \ W
  have hR : R ⊆ Q.erase e := exteriorBonds_subset_erase G Q W hc
  have hQR : Q.erase e = A ∪ R := by
    dsimp [A]; ext f; simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto
  have hAR : Disjoint A R := Finset.disjoint_sdiff.symm
  have hFB : F = W ∪ B := (Finset.union_sdiff_of_subset hW).symm
  have hWB : Disjoint W B := Finset.disjoint_sdiff
  conv_lhs => rw [hQR,bernoulliPolynomial_union A R hAR]
  trans bernoulliPolynomial A (fun a =>
    (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
      ((1-h)^W.card * finiteMarkedMoment G R B (cutOutside G W e) i h p)) p
  · apply bernoulliPolynomial_congr
    intro a ha
    trans bernoulliPolynomial R (fun b =>
      (if cluster G a x = (W : Set V) then (1:ℝ) else 0) * (1-h)^W.card *
        bernoulliPolynomial B (markedMomentValue G R (cutOutside G W e) i b) h) p
    · apply bernoulliPolynomial_congr
      intro b hb
      rw [hFB,bernoulliPolynomial_union W B hWB]
      trans bernoulliPolynomial W (fun u =>
        (if cluster G a x = (W : Set V) then (1:ℝ) else 0) *
        (if u = ∅ then (1:ℝ) else 0) *
        bernoulliPolynomial B (markedMomentValue G R (cutOutside G W e) i b) h) h
      · apply bernoulliPolynomial_congr
        intro u hu
        rw [← bernoulliPolynomial_const_mul]
        apply bernoulliPolynomial_congr
        intro v hv
        exact cutMomentValue_blocks G Q F W x e i a b u v ha hb hu hv
      · rw [bernoulliPolynomial_mul_const,bernoulliPolynomial_const_mul,
          bernoulliPolynomial_empty_indicator]
    · rw [bernoulliPolynomial_const_mul]
      exact mul_assoc _ _ _
  · rw [bernoulliPolynomial_mul_const]
    exact (mul_assoc _ _ _).symm

end CutFactor

section PointwiseRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

noncomputable def pivotalSuffixValue (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (i : ℕ) (ω : Finset E) (m : Finset V) : ℝ :=
  if OpenMarkedPivotal G ω m x e then
    markedMomentValue G (exteriorBonds G Q (cluster G (↑ω \ {e}) x))
      (cutOutside G (cluster G (↑ω \ {e}) x) e) i
      (exteriorBonds G ω (cluster G (↑ω \ {e}) x))
      (exteriorMarks m (cluster G (↑ω \ {e}) x)) else 0

 
theorem pivotalSuffixValue_insert (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (i : ℕ) (ω : Finset E) (he : e ∉ ω) (m : Finset V) :
    pivotalSuffixValue G Q x e i (insert e ω) m =
      if CutExists G (cluster G ω x) e then
        if Disjoint (cluster G ω x) (m : Set V) then
          markedMomentValue G (exteriorBonds G Q (cluster G ω x))
            (cutOutside G (cluster G ω x) e) i
            (exteriorBonds G ω (cluster G ω x)) (exteriorMarks m (cluster G ω x))
        else 0
      else 0 := by
  have hdel : ((insert e ω : Finset E) : Set E) \ {e} = (ω : Set E) := by
    simp [he]
  by_cases hc : CutExists G (cluster G ω x) e
  · obtain ⟨hab,ha,hb⟩ := cut_spec G (cluster G ω x) hc
    have heout := cut_not_exterior G (cluster G ω x) hc
    have hbe : exteriorBonds G (insert e ω) (cluster G ω x) = exteriorBonds G ω (cluster G ω x) := by
      ext f
      simp only [exteriorBonds,Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hf,hout⟩
        rcases hf with rfl | hf
        · exact (heout hout).elim
        · exact ⟨hf,hout⟩
      · exact fun h => ⟨Or.inr h.1,h.2⟩
    have hp := openMarkedPivotal_insert_cut G (ω : Set E) m (cluster G ω x) x rfl hab ha hb
    have hps : OpenMarkedPivotal G (insert e ω : Finset E) m x e ↔
        Disjoint (cluster G ω x) (m : Set V) ∧
        MarkedEvent G (exteriorBonds G ω (cluster G ω x))
          (exteriorMarks m (cluster G ω x)) (cutOutside G (cluster G ω x) e) := by
      simpa only [Finset.coe_insert,coe_exteriorBonds,coe_exteriorMarks] using hp
    simp only [pivotalSuffixValue,hdel,hbe,hc,ite_true,hps]
    by_cases hd : Disjoint (cluster G ω x) (m : Set V) <;>
      by_cases hm : MarkedEvent G (exteriorBonds G ω (cluster G ω x))
        (exteriorMarks m (cluster G ω x)) (cutOutside G (cluster G ω x) e) <;>
      simp only [markedMomentValue,hd,hm,and_true,and_false,ite_true,ite_false]
  · have hn : ¬OpenMarkedPivotal G (insert e ω : Finset E) m x e := by
      intro hp
      obtain ⟨a,b,hab,hxa,hxb,_⟩ := openMarkedPivotal_oriented G (insert e ω : Finset E) m x hp
      rw [hdel] at hxa hxb
      exact hc ⟨a,b,hab,hxa,hxb⟩
    simp only [pivotalSuffixValue,hn,hc,ite_false]

noncomputable def finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) : Finset V :=
  (cluster_finite_of_finite_edges G ω.finite_toSet x).toFinset

omit [Nonempty V] in
@[simp]
theorem coe_finiteRootComponent (G : BondGraph V E) (ω : Finset E) (x : V) :
    (finiteRootComponent G ω x : Set V) = cluster G ω x := by simp [finiteRootComponent]

omit [Nonempty V] in
theorem finiteRootComponent_subset (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteRootComponent G ω x ⊆ F := by
  intro y hy
  have hxy : Conn G (ω : Set E) x y := by
    change y ∈ (finiteRootComponent G ω x : Set V) at hy
    rwa [coe_finiteRootComponent] at hy
  exact hF (conn_mem_searchSupport G Q x (by exact_mod_cast hω) hxy)

omit [Nonempty V] in
 
theorem sum_component_partition (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (ω : Finset E) (hω : ω ⊆ Q) (hF : insert x (searchVertices G Q) ⊆ F)
    (f : Finset V → ℝ) :
    (∑ W ∈ F.powerset, if cluster G ω x = (W : Set V) then f W else 0) =
      f (finiteRootComponent G ω x) := by
  have hmem : finiteRootComponent G ω x ∈ F.powerset :=
    Finset.mem_powerset.mpr (finiteRootComponent_subset G Q F x ω hω hF)
  rw [Finset.sum_eq_single_of_mem _ hmem]
  · simp
  · intro W hW hne
    have hn : cluster G ω x ≠ (W : Set V) := by
      intro h
      apply hne
      apply Finset.coe_injective
      exact h.symm.trans (coe_finiteRootComponent G ω x).symm
    simp [hn]

 
theorem pivotalSuffixValue_component_sum (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (e : E) (i : ℕ) (ω : Finset E) (he : e ∉ ω) (hω : ω ⊆ Q)
    (hF : insert x (searchVertices G Q) ⊆ F) (m : Finset V) :
    pivotalSuffixValue G Q x e i (insert e ω) m = ∑ W ∈ F.powerset,
      if CutExists G W e then cutMomentValue G Q x e W i ω m else 0 := by
  rw [pivotalSuffixValue_insert G Q x e i ω he m]
  symm
  trans ∑ W ∈ F.powerset, if cluster G ω x = (W : Set V) then
    (if CutExists G W e then
      if Disjoint (W : Set V) (m : Set V) then
        markedMomentValue G (exteriorBonds G Q W) (cutOutside G W e) i
          (exteriorBonds G ω W) (exteriorMarks m W) else 0
      else 0) else 0
  · apply Finset.sum_congr rfl
    intro W _
    by_cases hc : CutExists G W e <;> by_cases hw : cluster G ω x = (W : Set V) <;>
      simp [cutMomentValue,hc,hw]
  · rw [sum_component_partition G Q F x ω hω hF]
    simp only [coe_finiteRootComponent]

omit [Nonempty V] in
 
theorem bernoulliPolynomial_open_gate (Q : Finset E) (e : E) (he : e ∈ Q)
    (f : Finset E → ℝ) (p : ℝ) (hf : ∀ ω ⊆ Q, e ∉ ω → f ω = 0) :
    bernoulliPolynomial Q f p =
      p*bernoulliPolynomial (Q.erase e) (fun ω => f (insert e ω)) p := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
  have hz : bernoulliPolynomial (Q.erase e) f p = 0 := by
    rw [← bernoulliPolynomial_zero (Q.erase e) p]
    apply bernoulliPolynomial_congr
    intro ω hω
    exact hf ω (Finset.Subset.trans hω (Finset.erase_subset e Q))
      (fun h => Finset.notMem_erase e Q (hω h))
  rw [hz,mul_zero,zero_add]

end PointwiseRecursion

section FiniteMomentRecursion
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty V]

 
noncomputable def cutCoefficient (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (h p : ℝ) : ℝ :=
  bernoulliPolynomial ((Q.erase e) \ exteriorBonds G Q W)
    (fun a => if cluster G a x = (W : Set V) then (1:ℝ) else 0) p * (1-h)^W.card

 
theorem finiteMarkedMoment_recursion (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : ℝ) (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x (i+1) h p = p * ∑ e ∈ Q, ∑ W ∈ F.powerset,
      if CutExists G W e then cutCoefficient G Q x e W h p *
        finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) i h p else 0 := by
  have hsum : finiteMarkedMoment G Q F x (i+1) h p =
      ∑ e ∈ Q, bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
        (pivotalSuffixValue G Q x e i ω) h) p := by
    change bernoulliPolynomial Q (fun ω => bernoulliPolynomial F
      (fun m => markedMomentValue G Q x (i+1) ω m) h) p = _
    simp only [markedMomentValue_succ_exterior,bernoulliPolynomial_sum]
    rfl
  rw [hsum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [bernoulliPolynomial_open_gate Q e he]
  · congr 1
    trans bernoulliPolynomial (Q.erase e) (fun ω => bernoulliPolynomial F
      (fun m => ∑ W ∈ F.powerset, if CutExists G W e then cutMomentValue G Q x e W i ω m else 0) h) p
    · apply bernoulliPolynomial_congr
      intro ω hω
      apply bernoulliPolynomial_congr
      intro m _
      exact pivotalSuffixValue_component_sum G Q F x e i ω
        (fun h => Finset.notMem_erase e Q (hω h))
        (Finset.Subset.trans hω (Finset.erase_subset e Q)) hF m
    · simp only [bernoulliPolynomial_sum]
      apply Finset.sum_congr rfl
      intro W hW
      by_cases hc : CutExists G W e
      · simp only [hc,ite_true]
        exact cutMoment_factor G Q F W x e i h p (Finset.mem_powerset.mp hW) hc
      · simp only [hc,ite_false,bernoulliPolynomial_zero]
  · intro ω hω heω
    rw [← bernoulliPolynomial_zero F h]
    apply bernoulliPolynomial_congr
    intro m _
    have hpiv : ¬OpenMarkedPivotal G ω m x e := fun h => heω h.1
    simp only [pivotalSuffixValue,hpiv,ite_false]

omit [Nonempty V] in
theorem cutCoefficient_nonneg (G : BondGraph V E) (Q : Finset E) (x : V)
    (e : E) (W : Finset V) (h p : unitInterval) : 0 ≤ cutCoefficient G Q x e W h p := by
  apply mul_nonneg
  · exact bernoulliPolynomial_nonneg _ _ _ p.2 (fun _ _ => by split_ifs <;> norm_num)
  · exact pow_nonneg (sub_nonneg.mpr h.2.2) _

omit [Nonempty V] in
theorem finiteMarkedMoment_nonneg (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (i : ℕ) (h p : unitInterval) : 0 ≤ finiteMarkedMoment G Q F x i h p := by
  apply bernoulliPolynomial_nonneg _ _ _ p.2
  intro ω _
  apply bernoulliPolynomial_nonneg _ _ _ h.2
  intro m _
  unfold markedMomentValue
  split_ifs <;> positivity

 
theorem exterior_mark_support (G : BondGraph V E) (Q : Finset E) (F W : Finset V)
    (x : V) (e : E) (he : e ∈ Q) (hc : CutExists G W e)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    insert (cutOutside G W e) (searchVertices G (exteriorBonds G Q W)) ⊆ F \ W := by
  have hs := cut_spec G W hc
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_of_mem
      (mem_searchVertices G he (by simp [hs.1]))),hs.2.2⟩
  · obtain ⟨f,hf,hyf⟩ := Finset.mem_biUnion.mp hy
    have hfQ := (Finset.mem_filter.mp hf).1
    have hfo := (Finset.mem_filter.mp hf).2
    have hyf' := Sym2.mem_toFinset.mp hyf
    exact Finset.mem_sdiff.mpr ⟨hF (Finset.mem_insert_of_mem
      (mem_searchVertices G hfQ hyf')),hfo y hyf'⟩

omit [Nonempty V] in
 
theorem exterior_degree_bound (G : BondGraph V E) (Q : Finset E) (W : Set V)
    (d : ℕ) (hd : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    ∀ v, ((exteriorBonds G Q W).filter (fun e => v ∈ G e)).card ≤ d := by
  intro v
  apply le_trans (Finset.card_le_card ?_) (hd v)
  intro e he
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
    (Finset.mem_filter.mp he).2⟩

 
theorem finiteMarkedMoment_geometric (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d) (i : ℕ)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) :
    finiteMarkedMoment G Q F x i h p ≤
      ((Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h))^i *
        finiteMarkedMoment G Q F x 0 h p := by
  let A : ℝ := (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr p.2.2))
    (Real.sqrt_nonneg _)
  change _ ≤ A^i * _
  induction i generalizing Q F x with
  | zero => simp
  | succ i ih =>
    have hpow := pow_nonneg hA i
    calc
      finiteMarkedMoment G Q F x (i+1) h p =
          (p:ℝ) * ∑ e ∈ Q, ∑ W ∈ F.powerset,
            if CutExists G W e then cutCoefficient G Q x e W h p *
              finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) i h p else 0 :=
        finiteMarkedMoment_recursion G Q F x i h p hF
      _ ≤ (p:ℝ) * ∑ e ∈ Q, ∑ W ∈ F.powerset,
            if CutExists G W e then cutCoefficient G Q x e W h p *
              (A^i * finiteMarkedMoment G (exteriorBonds G Q W) (F \ W) (cutOutside G W e) 0 h p)
              else 0 := by
        apply mul_le_mul_of_nonneg_left _ p.2.1
        apply Finset.sum_le_sum
        intro e he
        apply Finset.sum_le_sum
        intro W hW
        by_cases hc : CutExists G W e
        · simp only [hc,ite_true]
          apply mul_le_mul_of_nonneg_left _ (cutCoefficient_nonneg G Q x e W h p)
          exact ih _ _ _ (exterior_degree_bound G Q W d hdeg) (exterior_mark_support G Q F W x e he hc hF)
        · simp only [hc,ite_false,le_refl]
      _ = A^i * finiteMarkedMoment G Q F x 1 h p := by
        rw [show (1:ℕ) = 0+1 from rfl,finiteMarkedMoment_recursion G Q F x 0 h p hF]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro W hW
        by_cases hc : CutExists G W e <;> simp only [hc,ite_true,ite_false] <;> ring
      _ ≤ A^i * (A * finiteMarkedMoment G Q F x 0 h p) :=
        mul_le_mul_of_nonneg_left (finiteMarkedMoment_first_bound G Q F x p h hp hh d hd hdeg hF) hpow
      _ = A^(i+1) * finiteMarkedMoment G Q F x 0 h p := by rw [pow_succ]; ring

end FiniteMomentRecursion

section MarkedExponential
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem choose_generating_sum (n N : ℕ) (hn : n ≤ N) (z : ℝ) :
    (1+z)^n = ∑ i ∈ Finset.range (N+1), z^i*(n.choose i : ℝ) := by
  rw [add_comm (1:ℝ),add_pow]
  simp only [one_pow,mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
  intro i hi hin
  have hni : n < i := by simp only [Finset.mem_range,not_lt] at hin; omega
  simp [Nat.choose_eq_zero_of_lt hni]

 
theorem markedMomentValue_generating (G : BondGraph V E) (Q : Finset E) (x : V)
    (z : ℝ) (ω : Finset E) (m : Finset V) :
    (if MarkedEvent G ω m x then (1+z)^(markedOpenPivotals G Q x ω m).card else 0) =
      ∑ i ∈ Finset.range (Q.card+1), z^i*markedMomentValue G Q x i ω m := by
  by_cases hm : MarkedEvent G ω m x
  · simp only [markedMomentValue,hm,ite_true]
    exact choose_generating_sum _ _ (Finset.card_filter_le ..) z
  · simp only [markedMomentValue,hm,ite_false,mul_zero,Finset.sum_const_zero]

noncomputable def finiteMarkedGenerating (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (z h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x then (1+z)^(markedOpenPivotals G Q x ω m).card else 0) h) p

noncomputable def finiteMarkedTail (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (r : ℕ) (h p : ℝ) : ℝ :=
  bernoulliPolynomial Q (fun ω => bernoulliPolynomial F (fun m =>
    if MarkedEvent G ω m x ∧ r ≤ (markedOpenPivotals G Q x ω m).card then (1:ℝ) else 0) h) p

theorem finiteMarkedTail_nonneg (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (r : ℕ) (h p : unitInterval) : 0 ≤ finiteMarkedTail G Q F x r h p := by
  apply bernoulliPolynomial_nonneg _ _ _ p.2
  intro ω _
  apply bernoulliPolynomial_nonneg _ _ _ h.2
  intro m _
  split_ifs <;> norm_num

theorem finiteMarkedGenerating_eq (G : BondGraph V E) (Q : Finset E) (F : Finset V)
    (x : V) (z h p : ℝ) :
    finiteMarkedGenerating G Q F x z h p =
      ∑ i ∈ Finset.range (Q.card+1), z^i*finiteMarkedMoment G Q F x i h p := by
  simp only [finiteMarkedGenerating,markedMomentValue_generating,bernoulliPolynomial_sum,
    bernoulliPolynomial_const_mul]
  rfl

theorem half_geometric_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, (1/2:ℝ)^i) ≤ 2 := by
  have heq : (∑ i ∈ Finset.range N, (1/2:ℝ)^i) = 2*(1-(1/2:ℝ)^N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
  rw [heq]
  have := pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) N
  linarith

 
theorem finiteMarkedGenerating_le [Nonempty V] (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) (B : ℝ) (hB : 0 < B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) :
    finiteMarkedGenerating G Q F x (1/(2*B)) h p ≤ 2*finiteMarkedMoment G Q F x 0 h p := by
  let A : ℝ := (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h)
  have hA : 0 ≤ A := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr p.2.2))
    (Real.sqrt_nonneg _)
  have hb0 := finiteMarkedMoment_nonneg G Q F x 0 h p
  rw [finiteMarkedGenerating_eq]
  calc
    _ ≤ ∑ i ∈ Finset.range (Q.card+1), (1/(2*B))^i*(B^i*finiteMarkedMoment G Q F x 0 h p) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) i)
      apply (finiteMarkedMoment_geometric G p h hp hh d hd i Q F x hdeg hF).trans
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAB i) hb0
    _ = (∑ i ∈ Finset.range (Q.card+1), (1/2:ℝ)^i)*finiteMarkedMoment G Q F x 0 h p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_assoc,← mul_pow]
      congr 2
      field_simp
    _ ≤ 2*finiteMarkedMoment G Q F x 0 h p := mul_le_mul_of_nonneg_right (half_geometric_sum_le _) hb0

 
theorem finiteMarkedTail_markov (G : BondGraph V E) (p h : unitInterval) (Q : Finset E)
    (F : Finset V) (x : V) (z : ℝ) (hz : 0 ≤ z) (r : ℕ) :
    (1+z)^r * finiteMarkedTail G Q F x r h p ≤ finiteMarkedGenerating G Q F x z h p := by
  unfold finiteMarkedTail finiteMarkedGenerating
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ p.2
  intro ω hω
  rw [← bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono _ _ _ _ h.2
  intro m hm
  by_cases he : MarkedEvent G ω m x
  · by_cases hc : r ≤ (markedOpenPivotals G Q x ω m).card
    · simp only [he,hc,and_self,ite_true,mul_one]
      exact pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ 1+z) hc
    · simp only [he,hc,and_false,ite_true,ite_false,mul_zero]
      exact pow_nonneg (by linarith) _
  · simp only [he,false_and,ite_false,mul_zero,le_refl]

 
theorem log_one_add_half_inv_ge (B : ℝ) (hB : 1 ≤ B) :
    1/(4*B) ≤ Real.log (1+1/(2*B)) := by
  have hBp : 0 < B := by linarith
  let z : ℝ := 1/(2*B)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzle : z ≤ 2 := by dsimp [z]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  calc
    1/(4*B) = z/2 := by dsimp [z]; ring
    _ ≤ 2*z/(z+2) := by
      apply (le_div_iff₀ (by linarith : 0 < z+2)).mpr
      have hs := mul_le_mul_of_nonneg_right hzle hz
      nlinarith
    _ ≤ Real.log (1+z) := Real.le_log_one_add_of_nonneg hz

 
theorem finiteMarkedTail_exponential [Nonempty V] (G : BondGraph V E) (p h : unitInterval)
    (hp : (p:ℝ) < 1) (hh : 0 < (h:ℝ)) (d : ℕ) (hd : 0 < d)
    (Q : Finset E) (F : Finset V) (x : V)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d)
    (hF : insert x (searchVertices G Q) ⊆ F) (B : ℝ) (hB : 1 ≤ B)
    (hAB : (Real.sqrt ((d:ℝ)/2)/(1-p))*Real.sqrt (Real.log (1/(h:ℝ))/h) ≤ B) (r : ℕ) :
    finiteMarkedTail G Q F x r h p ≤
      2*Real.exp (-(r:ℝ)/(4*B))*finiteMarkedMoment G Q F x 0 h p := by
  have hBp : 0 < B := by linarith
  have hz : 0 ≤ 1/(2*B) := by positivity
  have hbase : 0 < 1+1/(2*B) := by positivity
  have hpow : Real.exp ((r:ℝ)/(4*B)) ≤ (1+1/(2*B))^r := by
    rw [← Real.exp_log (pow_pos hbase r),Real.log_pow]
    apply Real.exp_le_exp.mpr
    have hlog := mul_le_mul_of_nonneg_left (log_one_add_half_inv_ge B hB) (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    simpa only [mul_one_div] using hlog
  have hm := (finiteMarkedTail_markov G p h Q F x (1/(2*B)) hz r).trans
    (finiteMarkedGenerating_le G p h hp hh d hd Q F x hdeg hF B hBp hAB)
  have ht := finiteMarkedTail_nonneg G Q F x r h p
  have he := (mul_le_mul_of_nonneg_right hpow ht).trans hm
  calc
    finiteMarkedTail G Q F x r h p ≤ (2*finiteMarkedMoment G Q F x 0 h p)/Real.exp ((r:ℝ)/(4*B)) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using he)
    _ = 2*Real.exp (-(r:ℝ)/(4*B))*finiteMarkedMoment G Q F x 0 h p := by
      rw [neg_div,Real.exp_neg,div_eq_mul_inv]
      ring

end MarkedExponential

end Percolation

end OAI
