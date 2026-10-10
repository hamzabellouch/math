import OAI.Probability.FKMaps.CoreCompression

namespace OAI

noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] [Fintype β] in
lemma perm_preserves_range (f : α → β) {p : Perm α} {q : Perm β}
    (h : ∀ x,q (f x)=f (p x)) (y : β) : q y∈Set.range f ↔ y∈Set.range f := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨p⁻¹ x,q.injective ?_⟩
    rw [h]
    simpa using hx
  · rintro ⟨x,rfl⟩
    exact ⟨p x,(h x).symm⟩

omit [Fintype α] [Fintype β] in
lemma pow_intertwine (f : α → β) {p : Perm α} {q : Perm β}
    (h : ∀ x,q (f x)=f (p x)) (n : ℕ) (x : α) : (q^n) (f x)=f ((p^n) x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',pow_succ',mul_apply,mul_apply,ih,h]

lemma sameCycle_embedding (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) (x y : α) :
    p.SameCycle x y ↔ q.SameCycle (f x) (f y) := by
  constructor
  · intro hh
    obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
    exact ⟨(n:ℤ),by rw [zpow_natCast,pow_intertwine f h,hn]⟩
  · intro hh
    obtain ⟨n,hn⟩ := hh.exists_nat_pow_eq
    exact ⟨(n:ℤ),by simpa only [zpow_natCast] using hf ((pow_intertwine f h n x).symm.trans hn)⟩

def vertexEmbeddingEquiv (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) :
    Vertex p ≃ Side q (Set.range f) :=
  Quotient.congr (Equiv.ofInjective f hf) (sameCycle_embedding f hf h)

lemma vertexEmbeddingEquiv_vertex (f : α → β) (hf : Function.Injective f)
    {p : Perm α} {q : Perm β} (h : ∀ x,q (f x)=f (p x)) (x : α) :
    vertexEmbeddingEquiv f hf h (vertex p x)=sideMk q (Set.range f) (f x) ⟨x,rfl⟩ := rfl

/-- Relabelling literal darts, without adding edges or collapsing nonzero
original distances. -/
def dartGraphEmbeddingIso (f : α → β) (hf : Function.Injective f)
    {p e : Perm α} {q a : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (he : ∀ x,a (f x)=f (e x)) :
    dartGraph e p ≃g sideGraph a q (Set.range f) (perm_preserves_range f he) where
  toEquiv := vertexEmbeddingEquiv f hf hp
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne (congrArg (vertexEmbeddingEquiv f hf hp) h),?_⟩
      have go (x y : Vertex p) (d : β) (hd : d∈Set.range f)
          (hx : sideMk q (Set.range f) d hd=vertexEmbeddingEquiv f hf hp x)
          (hy : sideMk q (Set.range f) (a d) ((perm_preserves_range f he d).mpr hd)=
            vertexEmbeddingEquiv f hf hp y) :
          ∃ z,vertex p z=x ∧ vertex p (e z)=y := by
        obtain ⟨z,rfl⟩ := hd
        refine ⟨z,(vertexEmbeddingEquiv f hf hp).injective hx,?_⟩
        apply (vertexEmbeddingEquiv f hf hp).injective
        rw [vertexEmbeddingEquiv_vertex]
        simpa only [he] using hy
      rcases h with ⟨d,hd,hx,hy⟩|⟨d,hd,hy,hx⟩
      · exact Or.inl (go x y d hd hx hy)
      · exact Or.inr (go y x d hd hy hx)
    · rintro ⟨hne,h⟩
      refine ⟨fun h => hne ((vertexEmbeddingEquiv f hf hp).injective h),?_⟩
      have go (x y : Vertex p) (d : α) (hx : vertex p d=x) (hy : vertex p (e d)=y) :
          ∃ z,∃ hz : z∈Set.range f,sideMk q (Set.range f) z hz=vertexEmbeddingEquiv f hf hp x ∧
            sideMk q (Set.range f) (a z) ((perm_preserves_range f he z).mpr hz)=
              vertexEmbeddingEquiv f hf hp y := by
        refine ⟨f d,⟨d,rfl⟩,congrArg (vertexEmbeddingEquiv f hf hp) hx,?_⟩
        have hh := congrArg (vertexEmbeddingEquiv f hf hp) hy
        simpa only [vertexEmbeddingEquiv_vertex,he] using hh
      rcases h with ⟨d,hx,hy⟩|⟨d,hy,hx⟩
      · exact Or.inl (go x y d hx hy)
      · exact Or.inr (go y x d hy hx)

theorem dartGraph_embedding_edist (f : α → β) (hf : Function.Injective f)
    {p e : Perm α} {q a : Perm β}
    (hp : ∀ x,q (f x)=f (p x)) (he : ∀ x,a (f x)=f (e x)) (x y : α) :
    (dartGraph a q).edist (vertex q (f x)) (vertex q (f y))=
      (dartGraph e p).edist (vertex p x) (vertex p y) := by
  calc
    _=(sideGraph a q (Set.range f) (perm_preserves_range f he)).edist
        (sideMk q (Set.range f) (f x) ⟨x,rfl⟩) (sideMk q (Set.range f) (f y) ⟨y,rfl⟩) :=
      fullInclusion_edist (perm_preserves_range f hp) (perm_preserves_range f he) _ _
    _=_ := GraphWedge.iso_edist (dartGraphEmbeddingIso f hf hp he) (vertex p x) (vertex p y)

end FKCRT.PermutationWedge
namespace FKCRT.Inventory
open MapCycles PermutationWedge
attribute [local instance] Classical.propDecidable
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma formPerm_map_on (l : List α) (hn : l.Nodup) (f : α → β) (hf : Function.Injective f)
    (x : α) (hx : x∈l) : (l.map f).formPerm (f x)=f (l.formPerm x) := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hx
  simp only [List.get_eq_getElem]
  have hmap := List.formPerm_apply_getElem (l.map f) (hn.map hf) i.val (by simp)
  simpa only [List.getElem_map,List.length_map,List.formPerm_apply_getElem l hn] using hmap

lemma StackMatching.unique_first {w : α → TypedLetter} {l : List α}
    (M D : StackMatching w l) (hn : l.Nodup) : turns M.first=turns D.first := by
  obtain ⟨hE,_hF⟩ := typed_matchings_unique w l hn M.first M.second D.first D.second
    M.first_arches M.second_arches D.first_arches D.second_arches M.covers D.covers
    M.first_types M.second_types D.first_types D.second_types
  exact turns_perm hE ((M.covers.nodup_iff.mpr hn).sublist (by
    rw [endpoints_append];exact List.sublist_append_left _ _))

lemma StackMatching.unique_distance {w : α → TypedLetter} {l : List α}
    (M D : StackMatching w l) (hn : l.Nodup) (x y : α) : M.distance x y=D.distance x y := by
  unfold StackMatching.distance
  rw [M.unique_mate D hn,M.unique_first D hn]


lemma turns_map_total (f : α → β) (hf : Function.Injective f) (E : List (α×α))
    (hn : (endpoints E).Nodup) (i : α) :
    turns (E.map (Prod.map f f)) (f i)=f (turns E i) := by
  by_cases hi : i∈endpoints E
  · exact turns_map_on f hf E hn i hi
  · have hfi : f i∉endpoints (E.map (Prod.map f f)) := by
      rw [endpoints_map]
      intro h
      obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
      exact hi (hf hji ▸ hj)
    rw [turns_fixed_of_notMem hi,turns_fixed_of_notMem hfi]

lemma StackMatching.map_first {w : α → TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (f : α → β) (hf : Function.Injective f)
    (v : β → TypedLetter) (hv : ∀ i∈l,v (f i)=w i) (i : α) :
    turns (M.map f v hv).first (f i)=f (turns M.first i) := by
  apply turns_map_total f hf _ _ i
  exact (M.covers.nodup_iff.mpr hn).sublist (by
    rw [endpoints_append];exact List.sublist_append_left _ _)

lemma StackMatching.map_distance_of_full [Fintype α] [Fintype β]
    {w : α → TypedLetter} {l : List α}
    (M : StackMatching w l) (hn : l.Nodup) (hl : ∀ i,i∈l)
    (f : α → β) (hf : Function.Injective f) (v : β → TypedLetter)
    (hv : ∀ i∈l,v (f i)=w i) (i j : α) :
    (M.map f v hv).distance (f i) (f j)=M.distance i j := by
  apply dartGraph_embedding_edist f hf
  · intro x
    change (l.map f).formPerm (turns (M.map f v hv).first (f x))=
      f (l.formPerm (turns M.first x))
    rw [M.map_first hn f hf v hv,formPerm_map_on l hn f hf _ (hl _)]
  · intro x
    exact M.map_mate hn f hf v hv x (hl x)

/-- Compressing an actual isolated core/subtree to its ordered dart positions
preserves exact all-edge distances, not only its crossing graph. -/
theorem StackMatching.normalized_distance [Fintype α]
    {w : α → TypedLetter} {l : List α} (M : StackMatching w l) (hn : l.Nodup) :
    ∃ D : StackMatching (w ∘ l.get) (List.finRange l.length),
      ∀ i j,M.distance (l.get i) (l.get j)=D.distance i j := by
  have he : stackTypedRun ((List.finRange l.length).map (w ∘ l.get)) []=some [] := by
    rw [positions_word]
    exact M.empty hn
  let D := StackMatching.ofEmpty he
  let Q := D.map l.get w (fun _ _ => rfl)
  have hl : (List.finRange l.length).map l.get=l := List.map_get_finRange l
  let R : StackMatching w l := hl ▸ Q
  refine ⟨D,fun i j => ?_⟩
  rw [M.unique_distance R hn]
  change (hl ▸ Q).distance (l.get i) (l.get j)=_
  rw [StackMatching.distance_cast]
  exact D.map_distance_of_full (List.nodup_finRange _) (List.mem_finRange)
    l.get (List.nodup_iff_injective_get.mp hn) w (fun _ _ => rfl) i j

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- A connected nonempty typed core, expressed without an arbitrary pairing
choice: any matching certificate is the unique literal stack matching. -/
def CoreWord (w : List TypedLetter) : Prop :=
  ∃ (K : ℕ) (v : Fin K→TypedLetter) (M : StackMatching v (List.finRange K)),
    (List.finRange K).map v=w ∧
    ∃ r : Opener M.mate,r.val.val=0 ∧ ∀ x : Opener M.mate,(Chords.graph M.mate).Reachable r x

lemma coreWord_empty (w : List TypedLetter) (h : CoreWord w) : stackTypedRun w []=some [] := by
  obtain ⟨K,v,M,rfl,_⟩ := h
  exact M.empty (List.nodup_finRange K)

lemma coreWord_pos (w : List TypedLetter) (h : CoreWord w) : 0<w.length := by
  obtain ⟨K,v,M,rfl,r,_,_⟩ := h
  simpa only [List.length_map,List.length_finRange] using r.val.pos

lemma filter_finRange_eq (l : List (Fin N)) (hs : l.Pairwise (·<·)) :
    (List.finRange N).filter (fun d => decide (d∈l))=l := by
  apply ((List.pairwise_lt_finRange N).filter _).eq_of_mem_iff hs
  intro d
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]

lemma StackMatching.closed_subword (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (l : List (Fin N)) (hs : l.Pairwise (·<·))
    (hclosed : ∀ d∈l,M.mate d∈l) : stackTypedRun (l.map w) []=some [] := by
  let p : Fin N→Bool := fun d => decide (d∈l)
  have hn := List.nodup_finRange N
  have hp : ∀ d∈List.finRange N,p (M.mate d)=p d := by
    intro d _
    simp only [p,decide_eq_decide]
    constructor
    · intro hd
      have hh := hclosed (M.mate d) hd
      rwa [M.involutive hn] at hh
    · exact hclosed d
  have hh := (M.filter hn p hp).empty (hn.filter p)
  simpa only [p,filter_finRange_eq l hs] using hh

/-- The actual root component becomes a connected finite core after order
compression. No independence law or substituted matching is used. -/
theorem normalized_root_core (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (r : Opener M.mate) (hr : r.val.val=0) :
    CoreWord (((List.finRange N).filter (fun d => decide (d∈componentDarts M.mate r))).map w) := by
  let p : Fin N→Bool := fun d => decide (d∈componentDarts M.mate r)
  let l := (List.finRange N).filter p
  have hn := List.nodup_finRange N
  have ha := M.involutive hn
  have hp : ∀ d∈List.finRange N,p (M.mate d)=p d := by
    intro d _
    simp only [p,decide_eq_decide]
    exact componentDarts_mate M.mate ha r d
  let Q := M.filter hn p hp
  have hs : l.Pairwise (·<·) := (List.pairwise_lt_finRange N).filter p
  obtain ⟨P,hP⟩ := normalized_matching_mate w l hs Q
  let e := positionEmbedding l hs
  have hmatch : ∀ i,M.mate (e i)=e (P.mate i) := by
    intro i
    have hi : l.get i∈l := l.get_mem i
    have hpi : p (l.get i)=true := (List.mem_filter.mp hi).2
    exact (M.filter_mate hn p hp _ (List.mem_finRange _) hpi).symm.trans (hP i)
  have hrange : Set.range e={d | d∈componentDarts M.mate r} := by
    ext d
    change (∃ i,l.get i=d) ↔ d∈componentDarts M.mate r
    rw [← List.mem_iff_get]
    simp only [l,p,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq]
  have hrmem : r.val∈Set.range e := by
    rw [hrange]
    exact (mem_componentDarts _ _ _).mpr ⟨r,SimpleGraph.Reachable.refl r,Or.inl rfl⟩
  obtain ⟨s,hsr⟩ := opener_range M.mate P.mate e hmatch r hrmem
  have hs0 : s.val.val=0 := by
    have he : (e s.val).val=0 := (congrArg (fun x : Opener M.mate => x.val.val) hsr).trans hr
    by_contra hne
    have hlt : (⟨0,s.val.pos⟩ : Fin l.length)<s.val := by change 0<s.val.val;omega
    have hh := e.strictMono hlt
    have hv : (e ⟨0,s.val.pos⟩).val<(e s.val).val := hh
    omega
  refine ⟨l.length,w ∘ l.get,P,positions_word w l,s,hs0,?_⟩
  apply component_compression M.mate ha P.mate e hmatch s
  rw [hsr]
  exact hrange

/-- Canonical decomposition of every genuine nonempty successful word into
its root connected core and its literal successful corner words. -/
theorem successful_core_decomposition (w : Fin N→TypedLetter)
    (M : StackMatching w (List.finRange N)) (r : Opener M.mate) (hr : r.val.val=0) :
    let l := (rootSplit M.mate r).map (fun x => (w x.1,x.2.map w))
    cornerInsert l=(List.finRange N).map w ∧ CoreWord (l.map Prod.fst) ∧
    (∀ x∈l,stackTypedRun x.2 []=some [] ∧ x.2.length<N) ∧
    flexibleCount ((List.finRange N).map w) []=
      flexibleCount (l.map Prod.fst) []+(l.map (fun x => flexibleCount x.2 [])).sum := by
  dsimp only
  let l := (rootSplit M.mate r).map (fun x => (w x.1,x.2.map w))
  have hjoin : cornerInsert l=(List.finRange N).map w := by
    rw [cornerInsert_map,rootSplit_join M.mate r hr]
  have hske : l.map Prod.fst=
      ((List.finRange N).filter (fun d => decide (d∈componentDarts M.mate r))).map w := by
    change ((rootSplit M.mate r).map _).map _=_
    rw [List.map_map]
    have hh := congrArg (List.map w)
      (CornerSplit.skeleton (fun d => decide (d∈componentDarts M.mate r)) (List.finRange N))
    simpa only [List.map_map,Function.comp_def,rootSplit] using hh
  have hcore : CoreWord (l.map Prod.fst) := hske ▸ normalized_root_core w M r hr
  have hchunks : ∀ x∈l,stackTypedRun x.2 []=some [] ∧ x.2.length<N := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    refine ⟨?_,by rw [List.length_map];exact rootSplit_length_lt M.mate r y hy⟩
    apply M.closed_subword w y.2
    · obtain ⟨u,v,he,_⟩ := CornerSplit.located (fun d => decide (d∈componentDarts M.mate r))
        (List.finRange N) y hy
      have hs : (u++y.1::(y.2++v)).Pairwise (·<·) := he ▸ List.pairwise_lt_finRange N
      exact (List.pairwise_append.mp (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).2).1
    · exact rootSplit_closed M.mate (M.involutive (List.nodup_finRange N))
        (fun d => M.no_fixed (List.nodup_finRange N) d (List.mem_finRange d)) r hr y hy
  refine ⟨hjoin,hcore,hchunks,?_⟩
  rw [← hjoin]
  exact (cornerInsert_run_count l (fun x hx => (hchunks x hx).1) (coreWord_empty _ hcore)).2

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.CornerSplit
variable {α β : Type*}

lemma lift_join (f : α→β) (l : List (β×List β)) (u : List α)
    (hu : u.map f=join l) :
    ∃ L : List (α×List α),join L=u ∧ L.map (fun x => (f x.1,x.2.map f))=l := by
  induction l generalizing u with
  | nil =>
    have hu' : u=[] := List.map_eq_nil_iff.mp hu
    subst u
    exact ⟨[],rfl,rfl⟩
  | cons x l ih =>
    cases u with
    | nil => simp [join] at hu
    | cons a u =>
      change f a::u.map f=x.1::(x.2++join l) at hu
      obtain ⟨hx,hu⟩ := List.cons.inj hu
      obtain ⟨u1,u2,rfl,h1,h2⟩ := List.map_eq_append_iff.mp hu
      obtain ⟨L,hL,hm⟩ := ih u2 h2
      refine ⟨(a,u1)::L,?_,?_⟩
      · change a::(u1++join L)=a::(u1++u2)
        rw [hL]
      · simp only [List.map_cons,hx,h1,hm,Prod.eta]

lemma join_first_zero {N : ℕ} (l : List (Fin N×List (Fin N)))
    (hjoin : join l=List.finRange N) (i : Fin (l.map Prod.fst).length) (hi : i.val=0) :
    ((l.map Prod.fst).get i).val=0 := by
  cases l with
  | nil => exact Fin.elim0 i
  | cons x l =>
    cases N with
    | zero => exact Fin.elim0 x.1
    | succ N =>
      have hh : x.1=0 := by
        have hh := congrArg List.head? hjoin
        simpa only [join,List.flatMap_cons,List.cons_append,List.head?_cons,List.finRange_succ,
          List.map_cons,List.head?_map,Option.map_some,Fin.castSucc_zero,Option.some.injEq] using hh
      have hi' : i=⟨0,by simp⟩ := Fin.ext hi
      simp only [hi',List.map_cons,List.get_eq_getElem,List.getElem_cons_zero,hh,Fin.val_zero]

end FKCRT.CornerSplit
namespace FKCRT.Inventory
open MapCycles Chords
variable {N : ℕ}

/-- A genuinely connected typed core remains connected when its positions
are stretched by the actual corner inserts, including empty inserts. -/
theorem core_matching_at_positions (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hcore : CoreWord ((l.map Prod.fst).map w)) :
    ∃ C : StackMatching w (l.map Prod.fst),∃ r : Opener C.mate,
      r.val.val=0 ∧ ∀ x : Opener C.mate,(Chords.graph C.mate).Reachable r x := by
  obtain ⟨K,v,P,he,r,hr,hconnected⟩ := hcore
  have hk : K=(l.map Prod.fst).length := by
    have hh := congrArg List.length he
    simpa only [List.length_map,List.length_finRange] using hh
  subst K
  let L := l.map Prod.fst
  have hnjoin : (CornerSplit.join l).Nodup := hjoin.symm ▸ List.nodup_finRange N
  have hn : L.Nodup := hnjoin.sublist (CornerSplit.skeleton_sublist l)
  have hs : L.Pairwise (·<·) :=
    (hjoin.symm ▸ List.pairwise_lt_finRange N).sublist (CornerSplit.skeleton_sublist l)
  have hv : ∀ i,w (L.get i)=v i := by
    have hh : (List.finRange L.length).map v=(List.finRange L.length).map (w ∘ L.get) := by
      rw [positions_word];exact he
    intro i
    exact (List.map_inj_left.mp hh i (List.mem_finRange i)).symm
  let Q := P.map L.get w (fun i _ => hv i)
  have hL : (List.finRange L.length).map L.get=L := List.map_get_finRange L
  let C : StackMatching w L := hL ▸ Q
  have hC : C.mate=Q.mate := StackMatching.cast_mate hL Q
  let e := positionEmbedding L hs
  have hmatch : ∀ i,C.mate (e i)=e (P.mate i) := by
    intro i
    rw [hC]
    exact P.map_mate (List.nodup_finRange _) L.get (List.nodup_iff_injective_get.mp hn)
      w (fun i _ => hv i) i (List.mem_finRange i)
  let R := openerEmbedding C.mate P.mate e hmatch r
  refine ⟨C,R,CornerSplit.join_first_zero l hjoin r.val hr,?_⟩
  intro x
  have hx : x.val∈L := by
    apply C.covers.mem_iff.mp
    by_contra hx
    exact (ne_of_gt x.property) (turns_fixed_of_notMem hx)
  have hxr : x.val∈Set.range e := by
    change ∃ i,L.get i=x.val
    exact List.mem_iff_get.mp hx
  obtain ⟨y,hy⟩ := opener_range C.mate P.mate e hmatch x hxr
  rw [← hy]
  exact (hconnected y).map (Chords.graphHom C.mate P.mate e hmatch)

/-- Literal inverse with *normalized connected words* as cores. The graph
connectivity and the full matching are constructed from the words. -/
theorem core_word_insertion_inverse (w : Fin N→TypedLetter)
    (l : List (Fin N×List (Fin N))) (hjoin : CornerSplit.join l=List.finRange N)
    (hcore : CoreWord ((l.map Prod.fst).map w))
    (hw : ∀ x∈l,stackTypedRun (x.2.map w) []=some [])
    (M : StackMatching w (List.finRange N)) :
    ∃ r : Opener M.mate,r.val.val=0 ∧ rootSplit M.mate r=l := by
  obtain ⟨C,r,hr,hconn⟩ := core_matching_at_positions w l hjoin hcore
  obtain ⟨R,hR,hsplit⟩ := connected_corner_inverse w l hjoin hw
    M.first M.second C.first C.second M.first_arches M.second_arches M.covers
    M.first_types M.second_types C.first_arches C.second_arches C.covers
    C.first_types C.second_types r hr hconn
  exact ⟨R,(congrArg Fin.val hR).trans hr,hsplit⟩

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory
open MapCycles Chords

abbrev EmptyTypedWord := {w : List TypedLetter // stackTypedRun w []=some []}
abbrev NonemptyTypedWord := {w : EmptyTypedWord // w.val≠[]}

def ValidCorners (l : List (TypedLetter×List TypedLetter)) : Prop :=
  CoreWord (l.map Prod.fst) ∧ ∀ x∈l,stackTypedRun x.2 []=some []

lemma ValidCorners.empty {l : List (TypedLetter×List TypedLetter)} (h : ValidCorners l) :
    stackTypedRun (cornerInsert l) []=some [] :=
  (cornerInsert_run_count l h.2 (coreWord_empty _ h.1)).1

lemma ValidCorners.nonempty {l : List (TypedLetter×List TypedLetter)} (h : ValidCorners l) :
    cornerInsert l≠[] := by
  have hp := coreWord_pos _ h.1
  cases l with
  | nil => simp at hp
  | cons x l => simp [cornerInsert]

lemma core_lift_valid (l : List (TypedLetter×List TypedLetter)) (hl : ValidCorners l)
    {N : ℕ} (w : Fin N→TypedLetter) (L : List (Fin N×List (Fin N)))
    (hL : L.map (fun x => (w x.1,x.2.map w))=l) :
    CoreWord ((L.map Prod.fst).map w) ∧ ∀ x∈L,stackTypedRun (x.2.map w) []=some [] := by
  have he : (L.map Prod.fst).map w=l.map Prod.fst := by
    have hh := congrArg (List.map Prod.fst) hL
    simpa only [List.map_map,Function.comp_def] using hh
  refine ⟨he ▸ hl.1,?_⟩
  intro x hx
  exact hl.2 (w x.1,x.2.map w) (hL ▸ List.mem_map.mpr ⟨x,hx,rfl⟩)

/-- Rooted corner substitution is injective for the actual typed-word
inventory model, with every corner individually identified. -/
theorem valid_corner_injective {l r : List (TypedLetter×List TypedLetter)}
    (hl : ValidCorners l) (hr : ValidCorners r) (he : cornerInsert l=cornerInsert r) : l=r := by
  let w := cornerInsert l
  have hw := hl.empty
  have hwm : stackTypedRun ((List.finRange w.length).map w.get) []=some [] := by
    rw [List.map_get_finRange];exact hw
  let M := StackMatching.ofEmpty hwm
  obtain ⟨L,hL,hLm⟩ := CornerSplit.lift_join w.get l (List.finRange w.length) (List.map_get_finRange w)
  obtain ⟨R,hR,hRm⟩ := CornerSplit.lift_join w.get r (List.finRange w.length)
    ((List.map_get_finRange w).trans he)
  obtain ⟨hlc,hlw⟩ := core_lift_valid l hl w.get L hLm
  obtain ⟨hrc,hrw⟩ := core_lift_valid r hr w.get R hRm
  obtain ⟨a,ha,hsa⟩ := core_word_insertion_inverse w.get L hL hlc hlw M
  obtain ⟨b,hb,hsb⟩ := core_word_insertion_inverse w.get R hR hrc hrw M
  have hab : a=b := Subtype.ext (Fin.ext (ha.trans hb.symm))
  have hLR : L=R := by rw [← hsa,← hsb,hab]
  rw [← hLm,← hRm,hLR]

/-- Every nonempty successful typed word has its actual unique connected
core decomposition; children are strictly shorter, enabling recursion. -/
theorem exists_valid_corners (w : List TypedLetter) (hw : stackTypedRun w []=some [])
    (hne : w≠[]) :
    ∃ l : List (TypedLetter×List TypedLetter),ValidCorners l ∧ cornerInsert l=w ∧
      ∀ x∈l,x.2.length<w.length := by
  have hpos : 0<w.length := List.length_pos_iff.mpr hne
  have hwm : stackTypedRun ((List.finRange w.length).map w.get) []=some [] := by
    rw [List.map_get_finRange];exact hw
  let M := StackMatching.ofEmpty hwm
  let i : Fin w.length := ⟨0,hpos⟩
  have hni := M.no_fixed (List.nodup_finRange _) i (List.mem_finRange i)
  have hlt : i<M.mate i := by
    have hv := Fin.val_ne_of_ne hni
    change 0<(M.mate i).val
    change (M.mate i).val≠0 at hv
    omega
  let r : Opener M.mate := ⟨i,hlt⟩
  obtain ⟨hjoin,hcore,hchunks,_⟩ := successful_core_decomposition w.get M r rfl
  refine ⟨(rootSplit M.mate r).map (fun x => (w.get x.1,x.2.map w.get)),
    ⟨hcore,fun x hx => (hchunks x hx).1⟩,?_,fun x hx => (hchunks x hx).2⟩
  simpa only [List.map_get_finRange] using hjoin

abbrev CornerWords := {l : List (TypedLetter×List TypedLetter) // ValidCorners l}

def insertCornerWords (l : CornerWords) : NonemptyTypedWord :=
  ⟨⟨cornerInsert l.val,l.property.empty⟩,l.property.nonempty⟩

lemma insertCornerWords_bijective : Function.Bijective insertCornerWords := by
  constructor
  · intro l r h
    apply Subtype.ext
    exact valid_corner_injective l.property r.property (congrArg (fun w => w.val.val) h)
  · intro w
    obtain ⟨l,hl,he,_⟩ := exists_valid_corners w.val.val w.val.property w.property
    exact ⟨⟨l,hl⟩,Subtype.ext (Subtype.ext he)⟩

/-- Exact finite rooted corner-substitution bijection. This is not an
assumed block law, and it preserves all zero-size corner inserts. -/
def wordCornerEquiv : CornerWords ≃ NonemptyTypedWord :=
  Equiv.ofBijective insertCornerWords insertCornerWords_bijective

end FKCRT.Inventory
end


noncomputable section
open List Equiv Equiv.Perm
namespace FKCRT.Inventory

abbrev Core := {w : List TypedLetter // CoreWord w}
abbrev CornerData := Σ c : Core,Fin c.val.length→EmptyTypedWord

def cornerList (c : Core) (f : Fin c.val.length→List TypedLetter) :
    List (TypedLetter×List TypedLetter) := List.ofFn (fun i => (c.val.get i,f i))

lemma cornerList_fst (c : Core) (f : Fin c.val.length→List TypedLetter) :
    (cornerList c f).map Prod.fst=c.val := by
  rw [cornerList,List.map_ofFn]
  exact List.ofFn_get c.val

lemma cornerList_valid (c : Core) (f : Fin c.val.length→EmptyTypedWord) :
    ValidCorners (cornerList c (fun i => (f i).val)) := by
  refine ⟨?_,?_⟩
  · rw [cornerList_fst];exact c.property
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (f i).property

def cornersOfData (d : CornerData) : CornerWords :=
  ⟨cornerList d.1 (fun i => (d.2 i).val),cornerList_valid d.1 d.2⟩

def dataOfCorners (l : CornerWords) : CornerData :=
  ⟨⟨l.val.map Prod.fst,l.property.1⟩,fun i =>
    ⟨l.val[i.val].2,l.property.2 l.val[i.val] (List.getElem_mem _)⟩⟩

lemma cornersOfData_dataOfCorners (l : CornerWords) : cornersOfData (dataOfCorners l)=l := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp [cornersOfData,cornerList,dataOfCorners]
  · intro i hi hi'
    simp only [cornersOfData,cornerList,dataOfCorners,List.getElem_ofFn,
      List.get_eq_getElem,List.getElem_map,Prod.eta]

lemma cornerList_congr_core {c d : Core} {f : Fin c.val.length→List TypedLetter}
    {g : Fin d.val.length→List TypedLetter} (h : cornerList c f=cornerList d g) : c=d := by
  apply Subtype.ext
  have hh := congrArg (List.map Prod.fst) h
  simpa only [cornerList_fst] using hh

lemma cornerList_injective (c : Core) : Function.Injective (cornerList c) := by
  intro f g h
  have hh := List.ofFn_injective h
  funext i
  exact congrArg Prod.snd (congrFun hh i)

lemma cornersOfData_injective : Function.Injective cornersOfData := by
  rintro ⟨c,f⟩ ⟨d,g⟩ h
  have hh : cornerList c (fun i => (f i).val)=cornerList d (fun i => (g i).val) := congrArg Subtype.val h
  have hcd := cornerList_congr_core hh
  subst d
  have hfg := cornerList_injective c hh
  have hfg' : f=g := by
    funext i
    exact Subtype.ext (congrFun hfg i)
  subst g
  rfl

lemma dataOfCorners_cornersOfData (d : CornerData) : dataOfCorners (cornersOfData d)=d :=
  cornersOfData_injective (cornersOfData_dataOfCorners (cornersOfData d))

def cornerDataEquiv : CornerData ≃ CornerWords where
  toFun := cornersOfData
  invFun := dataOfCorners
  left_inv := dataOfCorners_cornersOfData
  right_inv := cornersOfData_dataOfCorners

/-- An exact product description of all nonempty genuine words. -/
def coreChildrenEquiv : CornerData ≃ NonemptyTypedWord := cornerDataEquiv.trans wordCornerEquiv

end FKCRT.Inventory
end

end OAI
