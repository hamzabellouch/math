import OAI.Combinatorics.MatchingEntropy.Contraction

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def supportSimple (G : LooplessGraph V E) (x : E → ℝ) : SimpleGraph V where
  Adj v w := ∃ e, 0 < x e ∧ ((G.left e=v ∧ G.right e=w) ∨ (G.left e=w ∧ G.right e=v))
  symm := ⟨by intro v w; rintro ⟨e,hx,h⟩; exact ⟨e,hx,h.symm⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨e,_,(⟨hl,hr⟩ | ⟨hl,hr⟩)⟩ <;> exact G.loopless e (hl.trans hr.symm)⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
 theorem supportSimple_edge (G : LooplessGraph V E) {x : E → ℝ} {e : E} (he : 0 < x e) :
    (G.supportSimple x).Adj (G.left e) (G.right e) := ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem sum_pred_le_one {C : Type uC} [Fintype C] (P : C → Prop) [DecidablePred P]
    (huniq : ∀ a b, P a → P b → a=b) : (∑ c, if P c then (1 : ℝ) else 0) ≤ 1 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a,ha⟩ := h
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [ite_eq_right]
      intro hPb
      exact hb (huniq b a hPb ha)
    · simp
  · simp only [not_exists] at h
    simp [h]

omit [Fintype V] [DecidableEq E] in

theorem odd_family_bound (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) {C : Type uC} [Fintype C] [DecidableEq C]
    (U : Finset V) (T : C → Finset V)
    (hodd : ∀ c, Odd (T c).card)
    (hdisj : ∀ c v, v ∈ T c → v ∉ U)
    (huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b)
    (hclosed : ∀ e, 0 < x e → G.left e ∉ U → G.right e ∉ U →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c) :
    Fintype.card C ≤ U.card := by
  have hcuts : (Fintype.card C : ℝ) ≤ ∑ c, G.cutMass x (T c) := by
    calc
      _ = ∑ c : C, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun c _ => hx.2.2 (T c) (hodd c)
  have hedges : ∀ e, (∑ c, if G.Crosses (T c) e then x e else 0) ≤
      (if G.left e ∈ U then x e else 0) + (if G.right e ∈ U then x e else 0) := by
    intro e
    by_cases hz : x e=0
    · simp [hz]
    have hp : 0 < x e := lt_of_le_of_ne (hx.1 e) (Ne.symm hz)
    by_cases hl : G.left e ∈ U <;> by_cases hr : G.right e ∈ U
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        rcases hc with h | h
        · exact hdisj c _ h.1 hl
        · exact hdisj c _ h.2 hr
      simp [hzero, hl, hr, hx.1 e]
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.right e ∈ T c := by
        intro c
        have hn : G.left e ∉ T c := fun h => hdisj c _ h hl
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.right e ∈ T c)
        (fun a b => huniq a b (G.right e))
      have heq' : (∑ c, if G.right e ∈ T c then x e else 0) =
          (∑ c, if G.right e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have heq : ∀ c, G.Crosses (T c) e ↔ G.left e ∈ T c := by
        intro c
        have hn : G.right e ∉ T c := fun h => hdisj c _ h hr
        simp [Crosses, hn]
      simp_rw [heq]
      have hcount := sum_pred_le_one (fun c => G.left e ∈ T c)
        (fun a b => huniq a b (G.left e))
      have heq' : (∑ c, if G.left e ∈ T c then x e else 0) =
          (∑ c, if G.left e ∈ T c then (1 : ℝ) else 0) * x e := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        split <;> simp
      rw [heq']
      simpa [hl, hr] using mul_le_mul_of_nonneg_right hcount (hx.1 e)
    · have hzero : ∀ c, ¬G.Crosses (T c) e := by
        intro c hc
        have hiff := hclosed e hp hl hr c
        unfold Crosses at hc
        tauto
      simp [hzero, hl, hr]
  have hdegree : ∑ v ∈ U, G.degree x v = (U.card : ℝ) := by
    simp_rw [hx.2.1]
    simp
  have hsum : (∑ e : E, ((if G.left e ∈ U then x e else 0) +
      (if G.right e ∈ U then x e else 0))) = ∑ v ∈ U, G.degree x v := by
    simp only [degree]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    have hf : ∀ v, (if G.Incident v e then x e else 0) =
        (if G.left e = v then x e else 0) + (if G.right e = v then x e else 0) := by
      intro v
      by_cases hl : G.left e=v <;> by_cases hr : G.right e=v
      · exact (G.loopless e (hl.trans hr.symm)).elim
      all_goals simp [Incident, hl, hr]
    simp_rw [hf]
    rw [Finset.sum_add_distrib]
    simp
  have hbound := (Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedges e))
  rw [hsum, hdegree] at hbound
  have hcutEq : (∑ c, G.cutMass x (T c)) = ∑ e, ∑ c, if G.Crosses (T c) e then x e else 0 := by
    simp only [cutMass, cut, Finset.sum_filter]
    exact Finset.sum_comm
  exact_mod_cast hcuts.trans (hcutEq ▸ hbound)

omit [DecidableEq E] in
theorem supportSimple_has_perfectMatching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : (G.supportSimple x).Subgraph, M.IsPerfectMatching := by
  classical
  apply SimpleGraph.tutte.mpr
  intro U
  let H := (⊤ : (G.supportSimple x).Subgraph).deleteVerts U
  let C := H.coe.oddComponents
  let : Fintype C := Fintype.ofFinite C
  let T : C → Finset V := fun c => (Subtype.val '' c.val.supp).toFinset
  have hnot : ∀ v : H.verts, v.val ∉ U := by
    intro v
    have hv := v.property
    simpa [H] using hv
  have hT : ∀ c : C, ∀ v : V, v ∈ T c ↔ ∃ w : H.verts, w ∈ c.val.supp ∧ w.val=v := by
    intro c v
    simp [T]
  have hodd : ∀ c : C, Odd (T c).card := by
    intro c
    have hc := c.property
    change Odd c.val.supp.ncard at hc
    change Odd ((Subtype.val '' c.val.supp).toFinset.card)
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hc
  have hdisj : ∀ c v, v ∈ T c → v ∉ U.toFinset := by
    intro c v hv
    obtain ⟨w,_,rfl⟩ := (hT c v).mp hv
    simpa using hnot w
  have huniq : ∀ a b v, v ∈ T a → v ∈ T b → a=b := by
    intro a b v ha hb
    obtain ⟨wa,hwa,rfl⟩ := (hT a v).mp ha
    obtain ⟨wb,hwb,he⟩ := (hT b wa.val).mp hb
    have hw : wb=wa := Subtype.ext he
    subst wb
    exact Subtype.ext (SimpleGraph.ConnectedComponent.eq_of_common_vertex hwa hwb)
  have hclosed : ∀ e, 0<x e → G.left e ∉ U.toFinset → G.right e ∉ U.toFinset →
      ∀ c, G.left e ∈ T c ↔ G.right e ∈ T c := by
    intro e he hl hr c
    have hl' : G.left e ∈ H.verts := by simpa [H] using hl
    have hr' : G.right e ∈ H.verts := by simpa [H] using hr
    have ha : H.Adj (G.left e) (G.right e) := by
      simpa [H, SimpleGraph.Subgraph.deleteVerts_adj] using
        And.intro hl (And.intro hr (G.supportSimple_edge he))
    change G.left e ∈ (Subtype.val '' c.val.supp).toFinset ↔
      G.right e ∈ (Subtype.val '' c.val.supp).toFinset
    simp only [Set.mem_toFinset]
    exact ⟨fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hr' ha,
      fun h => SimpleGraph.ConnectedComponent.mem_coe_supp_of_adj h hl' ha.symm⟩
  have hb := G.odd_family_bound hx U.toFinset T hodd hdisj huniq hclosed
  change ¬ U.ncard < H.coe.oddComponents.ncard
  have hcard : Fintype.card C = H.coe.oddComponents.ncard := by
    simp [C, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rw [hcard] at hb
  exact not_lt_of_ge (by simpa only [← Set.ncard_eq_toFinset_card'] using hb)

theorem exists_supported_matching (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) :
    ∃ M : G.Matching, ∀ e ∈ M.val, 0 < x e := by
  classical
  obtain ⟨M,hM⟩ := G.supportSimple_has_perfectMatching hx
  have he : ∀ q ∈ M.edgeSet, ∃ e, 0<x e ∧ s(G.left e,G.right e)=q := by
    intro q
    induction q using Sym2.inductionOn with
    | hf v w =>
      intro hq
      obtain ⟨e,he,hor⟩ := (SimpleGraph.Subgraph.mem_edgeSet.mp hq).adj_sub
      refine ⟨e,he,Sym2.eq_iff.mpr hor⟩
  let f : M.edgeSet → E := fun q => (he q.val q.property).choose
  have hf : ∀ q, 0<x (f q) ∧ s(G.left (f q),G.right (f q))=q.val :=
    fun q => (he q.val q.property).choose_spec
  let F : Finset E := Finset.univ.image f
  have hF : G.IsPerfectMatching F := by
    intro v
    obtain ⟨w,hw,hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    let q : M.edgeSet := ⟨s(v,w),SimpleGraph.Subgraph.mem_edgeSet.mpr hw⟩
    refine ⟨f q,⟨Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩,?_⟩,?_⟩
    · rcases Sym2.eq_iff.mp (hf q).2 with h | h
      · exact Or.inl h.1
      · exact Or.inr h.2
    · intro e he'
      obtain ⟨q',_,rfl⟩ := Finset.mem_image.mp he'.1
      have hq : q'=q := by
        apply Subtype.ext
        rcases he'.2 with hl | hr
        · have hval : q'.val=s(v,G.right (f q')) := by rw [← (hf q').2, hl]
          have hAdj : M.Adj v (G.right (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
        · have hval : q'.val=s(v,G.left (f q')) := by
            rw [← (hf q').2, hr, Sym2.eq_swap]
          have hAdj : M.Adj v (G.left (f q')) :=
            SimpleGraph.Subgraph.mem_edgeSet.mp (hval ▸ q'.property)
          rw [hval, hu _ hAdj]
      exact congrArg f hq
  refine ⟨⟨F,hF⟩,?_⟩
  intro e he'
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp he'
  exact (hf q).1

omit [Fintype V] [Fintype E] [DecidableEq E] in
@[simp] theorem crosses_singleton (G : LooplessGraph V E) (v : V) (e : E) :
    G.Crosses {v} e ↔ G.Incident v e := by
  have hh := G.loopless e
  simp only [Crosses, Finset.mem_singleton, Incident]
  have hn : ¬ (G.left e=v ∧ G.right e=v) := fun h => hh (h.1.trans h.2.symm)
  tauto

omit [Fintype V] [DecidableEq E] in
@[simp] theorem cutMass_singleton (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    G.cutMass x {v} = G.degree x v := by
  simp [cutMass,cut,Finset.sum_filter,degree]

omit [DecidableEq E] in

theorem constraint_eventually_line (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.constraintPolytope) (u : E → ℝ)
    (hzero : ∀ e, x e=0 → u e=0) (hdeg : ∀ v, G.degree u v=0)
    (hcut : ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0) :
    ∀ᶠ t : ℝ in 𝓝 0, x+t • u ∈ G.constraintPolytope := by
  have hn : ∀ᶠ t : ℝ in 𝓝 0, ∀ e, 0≤(x+t • u) e := by
    apply Filter.eventually_all.mpr
    intro e
    by_cases he : x e=0
    · exact Filter.Eventually.of_forall (by intro t; simp [he,hzero e he])
    · have hp : 0<x e := lt_of_le_of_ne (hx.1 e) (Ne.symm he)
      have hc : Continuous (fun t : ℝ => (x+t • u) e) := by fun_prop
      have hh : ∀ᶠ t : ℝ in 𝓝 0, 0<(x+t • u) e := (isOpen_lt continuous_const hc).mem_nhds
        (by simpa using hp : 0<(x+(0:ℝ) • u) e)
      exact hh.mono fun t ht => ht.le
  have hodd : ∀ᶠ t : ℝ in 𝓝 0, ∀ S : Finset V, Odd S.card → 1≤G.cutMass (x+t • u) S := by
    apply Filter.eventually_all.mpr
    intro S
    by_cases hS : Odd S.card
    · by_cases ht : G.cutMass x S=1
      · exact Filter.Eventually.of_forall (by
          intro t _
          have he := G.cutMass_linear x u 1 t S
          simp only [one_smul, one_mul, hcut S hS ht, mul_zero, add_zero, ht] at he
          exact he.ge)
      · have hp : 1<G.cutMass x S := lt_of_le_of_ne (hx.2.2 S hS) (Ne.symm ht)
        have hc : Continuous (fun t : ℝ => G.cutMass (x+t • u) S) :=
          (G.continuous_cutMass S).comp (by fun_prop)
        have hh : ∀ᶠ t : ℝ in 𝓝 0, 1<G.cutMass (x+t • u) S := (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using hp : 1<G.cutMass (x+(0:ℝ) • u) S)
        exact hh.mono fun t ht _ => ht.le
    · exact Filter.Eventually.of_forall fun _ h => (hS h).elim
  filter_upwards [hn,hodd] with t hn hodd
  refine ⟨hn,?_,hodd⟩
  intro v
  have he := G.degree_linear x u 1 t v
  simpa only [one_smul, one_mul, hdeg, mul_zero, add_zero, hx.2.1] using he

omit [Fintype V] [DecidableEq E] in
 theorem degree_sub (G : LooplessGraph V E) (x y : E → ℝ) (v : V) :
    G.degree (x-y) v = G.degree x v-G.degree y v := by
  have h := G.degree_linear x y 1 (-1) v
  simpa [sub_eq_add_neg] using h

omit [Fintype V] [DecidableEq E] in
 theorem cutMass_sub (G : LooplessGraph V E) (x y : E → ℝ) (S : Finset V) :
    G.cutMass (x-y) S = G.cutMass x S-G.cutMass y S := by
  have h := G.cutMass_linear x y 1 (-1) S
  simpa [sub_eq_add_neg] using h

omit [DecidableEq E] in

theorem trivial_tight_cut_preserved (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V))
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1)
    (u : E → ℝ) (hdeg : ∀ v, G.degree u v=0) :
    ∀ S, Odd S.card → G.cutMass x S=1 → G.cutMass u S=0 := by
  intro S hS ht
  have hc := odd_compl_of_even heven hS
  have hsmall : S.card=1 ∨ Sᶜ.card=1 := by
    have hn : ¬ (3≤S.card ∧ 3≤Sᶜ.card) := fun h => hnt ⟨S,hS,h.1,h.2,ht⟩
    rcases hS with ⟨k,hk⟩
    rcases hc with ⟨l,hl⟩
    omega
  rcases hsmall with hs | hs
  · obtain ⟨v,rfl⟩ := Finset.card_eq_one.mp hs
    simpa using hdeg v
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hs
    have hh : G.cutMass u Sᶜ=0 := by rw [hv,cutMass_singleton,hdeg]
    simpa only [cutMass,cut_compl] using hh

 theorem extreme_no_tight_integral (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hx : x ∈ Set.extremePoints ℝ G.constraintPolytope)
    (hnt : ¬∃ S : Finset V, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1) :
    ∃ M : G.Matching, G.indicator M=x := by
  have hxQ := (mem_extremePoints.mp hx).1
  obtain ⟨M,hM⟩ := G.exists_supported_matching hxQ
  have hd : ∀ v, G.degree (G.indicator M-x) v=0 := by
    intro v
    rw [degree_sub,degree_indicator,hxQ.2.1,sub_self]
  have hz : ∀ e, x e=0 → (G.indicator M-x) e=0 := by
    intro e he
    have hn : e ∉ M.val := fun h => (hM e h).ne' he
    simp [indicator,hn,he]
  have hu := G.constraint_eventually_line hxQ (G.indicator M-x) hz hd
    (G.trivial_tight_cut_preserved heven hnt _ hd)
  have he := extreme_point_direction_zero G.constraintPolytope hx _ hu
  exact ⟨M,sub_eq_zero.mp he⟩

theorem constraint_subset_polytope_aux (n : ℕ) :
    ∀ {W : Type uW} {F : Type uF} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n →
      G.constraintPolytope ⊆ G.polytope := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W F _ _ _ _ G hcard heven
    have heven' : Even (Fintype.card W) := hcard ▸ heven
    have hex : Set.extremePoints ℝ G.constraintPolytope ⊆ G.polytope := by
      intro x hx
      have hxQ := (mem_extremePoints.mp hx).1
      by_cases hcut : ∃ S : Finset W, Odd S.card ∧ 3≤S.card ∧ 3≤Sᶜ.card ∧ G.cutMass x S=1
      · obtain ⟨S,hS,hlo,hhi,ht⟩ := hcut
        have hc := odd_compl_of_even heven' hS
        have hlt1 : Fintype.card (Option {v // v ∈ S}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          omega
        have hlt2 : Fintype.card (Option {v // v ∈ Sᶜ}) < n := by
          simp only [Fintype.card_option,Fintype.card_coe]
          have hco := Finset.card_compl S
          have hle := Finset.card_le_univ S
          omega
        have hv1 : Even (Fintype.card (Option {v // v ∈ S})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hS.add_odd odd_one
        have hv2 : Even (Fintype.card (Option {v // v ∈ Sᶜ})) := by
          simpa only [Fintype.card_option,Fintype.card_coe] using hc.add_odd odd_one
        have hx1 := ih _ hlt1 (G.onSide S) rfl hv1 (G.restriction_mem_constraints hxQ S hS ht)
        have htc : G.cutMass x Sᶜ=1 := by simpa only [cutMass,cut_compl] using ht
        have hx2 := ih _ hlt2 (G.onSide Sᶜ) rfl hv2 (G.restriction_mem_constraints hxQ Sᶜ hc htc)
        obtain ⟨p,hp,hpx⟩ := ((G.onSide S).mem_polytope_iff _).mp hx1
        obtain ⟨q,hq,hqx⟩ := ((G.onSide Sᶜ).mem_polytope_iff _).mp hx2
        exact (G.mem_polytope_iff x).mpr (G.couple_laws S x hp hq (congrFun hpx) (congrFun hqx))
      · obtain ⟨M,rfl⟩ := G.extreme_no_tight_integral heven' hx hcut
        exact subset_convexHull ℝ _ (Set.mem_range_self M)
    rw [← closure_convexHull_extremePoints G.isCompact_constraintPolytope G.convex_constraintPolytope]
    exact closure_minimal (convexHull_min hex (convex_convexHull ℝ _)) G.compact_polytope.isClosed

theorem polytope_eq_constraints (G : LooplessGraph V E) (heven : Even (Fintype.card V)) :
    G.polytope = G.constraintPolytope := by
  exact Set.Subset.antisymm G.polytope_subset_constraintPolytope
    (constraint_subset_polytope_aux (Fintype.card V) G rfl heven)

end MatchingEntropyBounds.LooplessGraph

end

end OAI
