import OAI.Combinatorics.ListHadwiger.StageDeletion

namespace OAI

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure RoleRouting {V : Type} (G : SimpleGraph V) {t a : ℕ}
    (w : Fin t → V) (u : Fin a → V) (F H : Set V) (D : Finset V) (U : Set V) where
  fresh : Fin t → V
  fresh_injective : Function.Injective fresh
  fresh_mem : ∀ i, fresh i∈H
  target : Roles t a → ↥D
  route : ∀ p, G.Path (roleStart w u fresh p) (target p).val
  disjoint : ∀ p q, p≠q → Disjoint {v | v∈(route p).val.support} {v | v∈(route q).val.support}
  old_only : ∀ p v, v∈(route p).val.support → v∈F → ∃ i, p=Sum.inl i ∧ v=w i
  new_only : ∀ p v, v∈(route p).val.support → v∈H → ∃ i, p=Sum.inr (Sum.inr i) ∧ v=fresh i
  root_only : ∀ p j, u j∈(route p).val.support → u j=roleStart w u fresh p
  target_only : ∀ p v, v∈(route p).val.support → v∈D → v=(target p).val
  inside : ∀ p v, v∈(route p).val.support → v∈U

namespace RoleRouting
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {t a : ℕ}
    {w : Fin t → V} {u : Fin a → V} {F H U : Set V} {D : Finset V}

omit [DecidableEq V] in
lemma start_injective (R : RoleRouting G w u F H D U) :
    Function.Injective (roleStart w u R.fresh) := by
  intro p q he
  by_contra hpq
  exact Set.disjoint_left.mp (R.disjoint p q hpq) (R.route p).val.start_mem_support
    (Eq.mpr (congrArg (fun v => v∈(R.route q).val.support) he) (R.route q).val.start_mem_support)

omit [DecidableEq V] in
lemma target_injective (R : RoleRouting G w u F H D U) : Function.Injective R.target := by
  intro p q he
  by_contra hpq
  exact Set.disjoint_left.mp (R.disjoint p q hpq) (R.route p).val.end_mem_support
    (Eq.mpr (congrArg (fun v => v∈(R.route q).val.support) (congrArg Subtype.val he))
      (R.route q).val.end_mem_support)

theorem of_paired (hw : Function.Injective w) (hu : Function.Injective u)
    (hwu : ∀ i j, w i≠u j) (s : Fin t×Bool → V)
    (hs : Function.Injective s) (hsH : ∀ i, s i∈H)
    (hZH : Disjoint (↑(oldSources w u) : Set V) H)
    (P : PairedSources.Packing G
      (fun (i : ↥(oldSources w u)⊕Fin t) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D U)
    (hPF : ∀ p v, v∈(P.route p).val.support → v∈F → ∃ i, w i=v)
    (hPH : ∀ p v, v∈(P.route p).val.support → v∈H → ∃ i b, s (i,b)=v) :
    Nonempty (RoleRouting G w u F H D U) := by
  classical
  let e := roleEquiv w u hw hu hwu
  let w' : Fin t → V := fun i => s (i,P.choose (.inr i))
  let tar : Roles t a → ↥D := fun p => P.target (e p)
  have hstart (p : Roles t a) :
      Sum.elim Subtype.val (fun j => s (j,P.choose (e p))) (e p)=roleStart w u w' p := by
    rcases p with i | (j|i) <;> rfl
  let paths : ∀ p, G.Path (roleStart w u w' p) (tar p).val := fun p =>
    ⟨(P.route (e p)).val.copy (hstart p) rfl,by simp⟩
  have hsup (p : Roles t a) (v : V) : v∈(paths p).val.support ↔ v∈(P.route (e p)).val.support := by
    simp [paths]
  have hsource (p : Roles t a) (v : V) (hv : v∈(paths p).val.support)
      (hi : ∃ i b, v=Sum.elim Subtype.val (fun j => s (j,b)) i) : v=roleStart w u w' p :=
    (P.source_only (e p) v ((hsup p v).mp hv) hi).trans (hstart p)
  have hxinj : Function.Injective (roleStart w u w') := by
    intro p q he
    apply e.injective
    apply P.source_injective
    exact (hstart p).trans (he.trans (hstart q).symm)
  refine ⟨⟨w',?_,fun i => hsH _,tar,paths,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j he
    exact congrArg Prod.fst (hs he)
  · intro p q hpq
    apply Set.disjoint_left.mpr
    intro v hv hw'
    exact Set.disjoint_left.mp (P.disjoint _ _ (fun he => hpq (e.injective he)))
      ((hsup p v).mp hv) ((hsup q v).mp hw')
  · intro p v hv hvF
    obtain ⟨i,hi⟩ := hPF (e p) v ((hsup p v).mp hv) hvF
    have he := hsource p v hv ⟨e (.inl i),false,by simpa [e,roleEquiv,roleTo] using hi.symm⟩
    refine ⟨i,hxinj ?_,hi.symm⟩
    exact he.symm.trans hi.symm
  · intro p v hv hvH
    obtain ⟨i,b,hi⟩ := hPH (e p) v ((hsup p v).mp hv) hvH
    have he := hsource p v hv ⟨Sum.inr i,b,hi.symm⟩
    rcases p with j | (j|j)
    · have he' : v=w j := he
      exact (Set.disjoint_left.mp hZH ((mem_oldSources w u _).mpr (Or.inl ⟨j,rfl⟩))
        (he' ▸ hvH)).elim
    · have he' : v=u j := he
      exact (Set.disjoint_left.mp hZH ((mem_oldSources w u _).mpr (Or.inr ⟨j,rfl⟩))
        (he' ▸ hvH)).elim
    · exact ⟨j,rfl,he⟩
  · intro p j hv
    exact hsource p (u j) hv ⟨e (.inr (.inl j)),false,rfl⟩
  · intro p v hv hvD
    exact P.target_only (e p) v ((hsup p v).mp hv) hvD
  · intro p v hv
    exact P.inside (e p) v ((hsup p v).mp hv)

theorem weave (R : RoleRouting G w u F H D U) (J : Set V) {b : ℕ}
    (hJ : WovenOn G J a b) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (hc : 2*t+a≤b) (hJF : Disjoint J F) (hJH : Disjoint J H)
    (hJD : Disjoint J (↑D : Set V)) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ R' : RoleRouting G w u F H D (U∪J), R'.fresh=R.fresh ∧
      ∀ p j v, v∈(R'.route p).val.support → v∈M.branch j → p=Sum.inr (Sum.inl j) := by
  have hcard : Fintype.card (Roles t a)≤b := by simpa [Roles,show t+(a+t)=2*t+a by omega] using hc
  obtain ⟨M,hMJ,Q,hQQ,hQP,hQM⟩ := reroute_sources J hJ u hu huJ
    (roleStart w u R.fresh) (fun p => (R.target p).val) R.route hcard R.disjoint R.root_only
  let R' : RoleRouting G w u F H D (U∪J) :=
    { fresh := R.fresh
      fresh_injective := R.fresh_injective
      fresh_mem := R.fresh_mem
      target := R.target
      route := Q
      disjoint := hQQ
      old_only := fun p v hv hvF => R.old_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJF hvJ hvF)) hvF
      new_only := fun p v hv hvH => R.new_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJH hvJ hvH)) hvH
      root_only := fun p j hv => (hQM p j (u j) hv (M.root_mem j)).1
      target_only := fun p v hv hvD => R.target_only p v
        (hQP p v hv (fun hvJ => Set.disjoint_left.mp hJD hvJ hvD)) hvD
      inside := fun p v hv => by
        by_cases hvJ : v∈J
        · exact Or.inr hvJ
        · exact Or.inl (R.inside p v (hQP p v hv hvJ)) }
  refine ⟨M,hMJ,R',rfl,?_⟩
  intro p j v hv hvm
  obtain ⟨he,he'⟩ := hQM p j v hv hvm
  exact R.start_injective (he.symm.trans he')

end RoleRouting
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset Footprint
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t a : ℕ}

theorem combine_systems (F H D : Finset V) (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j)
    (hwF : ∀ i, w i∈F) (hZH : Disjoint (oldSources w u) H)
    (hZD : Disjoint (oldSources w u) D) (hHD : Disjoint H D)
    (R : System G) (hRU : R.domain=univ\(F\univ.image w))
    (P : DoublePacking G (oldSources w u) D)
    (hPR : ∀ i v, v∈(P.route i).val.support → v∈R.used)
    (hRH : Disjoint R.used H)
    (Q : Second G (univ\(F∪univ.image u)) H D (2*t)) :
    Nonempty (RoleRouting G w u (↑F : Set V) (↑H : Set V) D
      (↑(R.used∪Q.record.used) : Set V)) := by
  classical
  let e : (Fin t×Bool) ≃ Fin (2*t) := Fintype.equivOfCardEq (by simp; omega)
  let s : Fin t×Bool → V := Q.source ∘ e
  let tar : Fin t×Bool → ↥D := Q.target ∘ e
  let paths : ∀ i, G.Path (s i) (tar i).val := fun i => Q.route (e i)
  have hs : Function.Injective s := Q.source_injective.comp e.injective
  have hsH : ∀ i, s i∈H := fun i => Q.source_mem (e i)
  have hPH : ∀ i v, v∈(P.route i).val.support → v∉H :=
    fun i v hv hH => Finset.disjoint_left.mp hRH (hPR i v hv) hH
  have hQZ : ∀ i v, v∈(paths i).val.support → v∉oldSources w u := by
    intro i v hv hvZ
    have hdom := (mem_sdiff.mp (Q.route_domain (e i) hv)).2
    rcases (mem_oldSources w u v).mp hvZ with ⟨j,rfl⟩|⟨j,rfl⟩
    · exact hdom (mem_union_left _ (hwF j))
    · exact hdom (mem_union_right _ (mem_image.mpr ⟨j,mem_univ _,rfl⟩))
  obtain ⟨K⟩ := combine_double P s tar paths hs hsH hZH hZD hHD hPH hQZ
    (fun i v hv hvH => Q.source_only (e i) v hv hvH)
    (fun i j hij => Q.disjoint _ _ (fun he => hij (e.injective he)))
  have hinside (i) (v) (hv : v∈(K.route i).val.support) : v∈R.used∪Q.record.used := by
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · exact mem_union_left _ (hPR j v hj)
    · exact mem_union_right _ ((Q.mem_record_used v).mpr ⟨e j,hj⟩)
  let K' : PairedSources.Packing G
      (fun (i : ↥(oldSources w u)⊕Fin t) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D
      (↑(R.used∪Q.record.used) : Set V) :=
    { choose := K.choose
      target := K.target
      route := K.route
      disjoint := K.disjoint
      source_only := K.source_only
      target_only := K.target_only
      inside := hinside }
  apply RoleRouting.of_paired hw hu hwu s hs hsH (by exact_mod_cast hZH) K'
  · intro i v hv hvF
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · have hdom := R.used_subset_domain (hPR j v hj)
      rw [hRU] at hdom
      have hvW : v∈univ.image w := by
        by_contra hn
        exact (mem_sdiff.mp hdom).2 (mem_sdiff.mpr ⟨hvF,hn⟩)
      simpa only [mem_image,mem_univ,true_and] using hvW
    · exact False.elim ((mem_sdiff.mp (Q.route_domain (e j) hj)).2 (mem_union_left _ hvF))
  · intro i v hv hvH
    rcases K.inside i v hv with ⟨j,hj⟩|⟨j,hj⟩
    · exact False.elim (hPH j v hj hvH)
    · exact ⟨j.1,j.2,(Q.source_only (e j) v hj hvH).symm⟩

omit [Fintype V] in
lemma Second.used_inter_region (F H D : Finset V) {n : ℕ}
    (Q : Second G F H D n) : Q.record.used∩H=Q.record.starts := by
  rw [Q.record_starts]
  ext v
  simp only [mem_inter,Q.mem_record_used,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨⟨i,hi⟩,hvH⟩
    exact ⟨i,(Q.source_only i v hi hvH).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨i,(Q.route i).val.start_mem_support⟩,Q.source_mem i⟩

omit [Fintype V] in
lemma Second.starts_card (F H D : Finset V) {n : ℕ}
    (Q : Second G F H D n) : Q.record.starts.card=n := by
  rw [Q.record_starts,card_image_of_injective _ Q.source_injective,card_univ,Fintype.card_fin]

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma union_connected {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V} {k : ℕ}
    (hA : KConnectedOn G A k) (hB : KConnectedOn G B k)
    (hAB : k ≤ (A∩B).card) : KConnectedOn G (A∪B) k := by
  classical
  refine ⟨hA.1.trans_le (card_le_card subset_union_left),?_⟩
  intro Z _ hZ
  have hZA : (Z∩A).card < k := (card_le_card inter_subset_left).trans_lt hZ
  have hZB : (Z∩B).card < k := (card_le_card inter_subset_left).trans_lt hZ
  have hAc := hA.2 (Z∩A) inter_subset_right hZA
  have hBc := hB.2 (Z∩B) inter_subset_right hZB
  have hn : ((A∩B)\Z).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    have hs : A∩B ⊆ Z := sdiff_eq_empty_iff_subset.mp he
    have hh := card_le_card hs
    omega
  obtain ⟨v,hv⟩ := hn
  have hvA : v∈A\(Z∩A) := by simpa using (show v∈A ∧ v∉Z from
    ⟨(mem_inter.mp (mem_sdiff.mp hv).1).1,(mem_sdiff.mp hv).2⟩)
  have hvB : v∈B\(Z∩B) := by simpa using (show v∈B ∧ v∉Z from
    ⟨(mem_inter.mp (mem_sdiff.mp hv).1).2,(mem_sdiff.mp hv).2⟩)
  have he : (↑((A∪B)\Z):Set V) = (↑(A\(Z∩A)):Set V) ∪ (↑(B\(Z∩B)):Set V) := by
    ext w
    simp only [mem_coe,mem_sdiff,mem_union,mem_inter,Set.mem_union]
    tauto
  rw [he]
  exact SimpleGraph.induce_union_connected hAc.preconnected hBc.preconnected ⟨v,hvA,hvB⟩

def attached {V P : Type} {G : SimpleGraph V} (C : P → Set V)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (p : P) : Set V :=
  C p ∪ {v | v∈(paths p).val.support}

def extended {V P I : Type} {G : SimpleGraph V} (E : I → Set V) (C : P → Set V)
    (owner : P → I) (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (i : I) : Set V :=
  E i ∪ {v | ∃ p, owner p=i ∧ v∈attached C x y paths p}

lemma attached_connected {V P : Type} {G : SimpleGraph V} (C : P → Set V)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hC : ∀ p, (G.induce (C p)).Connected) (hx : ∀ p, x p∈C p) (p : P) :
    (G.induce (attached C x y paths p)).Connected :=
  SimpleGraph.induce_union_connected (hC p).preconnected
    (paths p).val.connected_induce_support.preconnected ⟨x p,hx p,(paths p).val.start_mem_support⟩

lemma extended_connected {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hE : ∀ i, (G.induce (E i)).Connected)
    (hC : ∀ p, (G.induce (C p)).Connected)
    (hx : ∀ p, x p∈C p) (hy : ∀ p, y p∈E (owner p)) (i : I) :
    (G.induce (extended E C owner x y paths i)).Connected := by
  obtain ⟨u,hu⟩ := (hE i).nonempty
  apply G.induce_connected_of_patches u (Or.inl hu)
  intro v hv
  rcases hv with hv | ⟨p,hpi,hvp⟩
  · exact ⟨E i,Set.subset_union_left,hu,hv,(hE i).preconnected _ _⟩
  · have hc := SimpleGraph.induce_union_connected (hE i).preconnected
      (attached_connected C x y paths hC hx p).preconnected
      ⟨y p,hpi ▸ hy p,Or.inr (paths p).val.end_mem_support⟩
    refine ⟨E i ∪ attached C x y paths p,?_,Or.inl hu,Or.inr hvp,hc.preconnected _ _⟩
    intro w hw
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨p,hpi,hw⟩

lemma extended_disjoint {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p))
    (hE : ∀ i j, i≠j → Disjoint (E i) (E j))
    (hC : ∀ p q, owner p≠owner q → Disjoint (C p) (C q))
    (hEC : ∀ i p, i≠owner p → Disjoint (E i) (C p))
    (hEP : ∀ i p, i≠owner p → Disjoint (E i) {v | v∈(paths p).val.support})
    (hCP : ∀ p q, owner p≠owner q → Disjoint (C p) {v | v∈(paths q).val.support})
    (hP : ∀ p q, owner p≠owner q → Disjoint {v | v∈(paths p).val.support}
      {v | v∈(paths q).val.support}) :
    ∀ i j, i≠j → Disjoint (extended E C owner x y paths i) (extended E C owner x y paths j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv | ⟨p,hpi,hvp|hvp⟩ <;> rcases hw with hw | ⟨q,hqj,hvq|hvq⟩
  · exact Set.disjoint_left.mp (hE i j hij) hv hw
  · exact Set.disjoint_left.mp (hEC i q (hqj ▸ hij)) hv hvq
  · exact Set.disjoint_left.mp (hEP i q (hqj ▸ hij)) hv hvq
  · exact Set.disjoint_left.mp (hEC j p (hpi ▸ Ne.symm hij)) hw hvp
  · exact Set.disjoint_left.mp (hC p q (by simpa only [hpi,hqj] using hij)) hvp hvq
  · exact Set.disjoint_left.mp (hCP p q (by simpa only [hpi,hqj] using hij)) hvp hvq
  · exact Set.disjoint_left.mp (hEP j p (hpi ▸ Ne.symm hij)) hw hvp
  · exact Set.disjoint_left.mp (hCP q p (by simpa only [hpi,hqj] using Ne.symm hij)) hvq hvp
  · exact Set.disjoint_left.mp (hP p q (by simpa only [hpi,hqj] using hij)) hvp hvq

lemma satellite_subset {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (p : P) :
    C p ⊆ extended E C owner x y paths (owner p) :=
  fun _ hv => Or.inr ⟨p,rfl,Or.inl hv⟩

lemma path_subset {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (p : P) :
    {v | v∈(paths p).val.support} ⊆ extended E C owner x y paths (owner p) :=
  fun _ hv => Or.inr ⟨p,rfl,Or.inr hv⟩

lemma extended_subset {V P I : Type} {G : SimpleGraph V}
    (E : I → Set V) (C : P → Set V) (owner : P → I)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) {F : Set V}
    (hE : ∀ i, E i ⊆ F) (hC : ∀ p, C p ⊆ F)
    (hP : ∀ p v, v∈(paths p).val.support → v∈F) (i : I) :
    extended E C owner x y paths i ⊆ F := by
  rintro v (hv|⟨p,_,hv|hv⟩)
  · exact hE i hv
  · exact hC p hv
  · exact hP p v hv

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem grouped_ends {V P I : Type} [Fintype V] [DecidableEq V]
    [Fintype P] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (D : Finset V) (y : P → V)
    (hy : Function.Injective y) (hyD : ∀ p, y p∈D)
    (owner : P → I) (hs : Function.Surjective owner)
    (hp : 1≤Fintype.card P) (hc : KConnectedOn G D (65536*Fintype.card P)) :
    ∃ E : I → Set V,
      (∀ i, (G.induce (E i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (E i) (E j)) ∧
      (∀ i, E i⊆(↑D : Set V)) ∧ ∀ p, y p∈E (owner p) := by
  classical
  let yr : P → ↥D := fun p => ⟨y p,hyD p⟩
  have hyr : Function.Injective yr := fun _ _ he => hy (congrArg Subtype.val he)
  let A : Finset ↥D := univ.image yr
  have hAc : A.card=Fintype.card P := by rw [card_image_of_injective _ hyr,card_univ]
  have ha (p : P) : yr p∈A := mem_image.mpr ⟨p,mem_univ _,rfl⟩
  have hpre : ∀ a : ↥A, ∃ p, yr p=a.val := by
    intro a
    obtain ⟨p,_,he⟩ := mem_image.mp a.property
    exact ⟨p,he⟩
  choose idx hidx using hpre
  have hi (p : P) : idx ⟨yr p,ha p⟩=p := hyr (hidx ⟨yr p,ha p⟩)
  let lab : ↥A → I := fun a => owner (idx a)
  have hls : Function.Surjective lab := by
    intro i
    obtain ⟨p,rfl⟩ := hs i
    exact ⟨⟨yr p,ha p⟩,congrArg owner (hi p)⟩
  have hc' : KConnectedOn (G.induce (↑D : Set V)) univ (65536*A.card) := by
    rw [hAc]
    exact Knitting.induce_connected G D hc
  obtain ⟨E,hE,hEE,hterm⟩ := Knitting.group_terminals (G.induce (↑D : Set V)) A lab hls
    (by omega) hc'
  let M := Knitting.model_induce G D
  refine ⟨fun i => M.expand (E i),fun i => M.expand_connected (hE i),
    fun i j hij => M.expand_disjoint (hEE i j hij),?_,?_⟩
  · intro i v hv
    obtain ⟨w,_,hw⟩ := hv
    have he : v=w.val := hw
    exact he ▸ w.property
  · intro p
    refine ⟨yr p,?_,rfl⟩
    simpa only [lab,hi] using hterm ⟨yr p,ha p⟩

end LinearListHadwiger.Stage

end OAI
