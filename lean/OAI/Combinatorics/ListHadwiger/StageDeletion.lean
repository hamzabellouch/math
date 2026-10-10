import OAI.Combinatorics.ListHadwiger.StageExtension

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph Footprint
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
lemma under_mono {U A B : Finset V} (h : A⊆B) : under U A⊆under U B := by
  intro v hv
  exact (mem_under v).mpr (h ((mem_under v).mp hv))

omit [Fintype V] in

theorem first_system (U S Z D : Finset V)
    (hSU : S⊆U) (hZS : Z⊆S) (hDS : D⊆S) (hZD : Disjoint Z D)
    (hc : KConnectedOn G S (2*Z.card)) (hd : 2*Z.card≤D.card) :
    ∃ R : System G, ∃ P : DoublePacking G Z D,
      R.domain=U ∧ R.n=2*Z.card ∧ R.starts=Z ∧ R.ends⊆D ∧
      ∀ i v, v∈(P.route i).val.support → v∈R.used := by
  have hZU := hZS.trans hSU
  have hDU := hDS.trans hSU
  let A := under U Z
  let B := under U D
  have hconn : KConnectedOn (G.induce (↑U : Set V)) (under U S) (2*A.card) := by
    simpa only [A,under_card hZU] using under_connected G hSU hc
  obtain ⟨P₀⟩ := DoublePacking.in_region (under U S) A B (under_mono hZS) (under_mono hDS)
    (under_disjoint hZD) hconn (by simpa only [A,B,under_card hZU,under_card hDU] using hd)
  obtain ⟨Q,hQ⟩ := DoublePacking.exists_minimal ⟨P₀⟩
  let R := System.ofMinimal U (fun i : ↥A×Bool => i.1.val) B Q hQ
  let P₁ := DoublePacking.ofMinimal Q hQ (under_disjoint hZD)
  let P := P₁.lift hZU hDU
  refine ⟨R,P,rfl,?_,?_,?_,?_⟩
  · change Fintype.card (↥A×Bool)=2*Z.card
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,A,under_card hZU]
    omega
  · rw [System.ofMinimal_starts]
    ext v
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_under _).mp i.1.property
    · intro hv
      exact ⟨(⟨⟨v,hZU hv⟩,(mem_under _).mpr hv⟩,false),rfl⟩
  · intro v hv
    have hh := System.ofMinimal_ends U (fun i : ↥A×Bool => i.1.val) B Q hQ hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hh
    exact (mem_under _).mp hw
  · intro i v hv
    obtain ⟨w,hw,he⟩ := (DoublePacking.mem_lift_route hZU hDU P₁ i v).mp hv
    have hw' : w∈(Q.paths (DoublePacking.liftIndex hZU i)).2.val.support := by
      simpa only [P₁,DoublePacking.ofMinimal_support] using hw
    exact (System.mem_ofMinimal_used U _ B Q hQ v).mpr ⟨_,w,hw',he⟩

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph Footprint
attribute [local instance] Classical.propDecidable

structure Second {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U H D : Finset V) (n : ℕ) where
  sys : Unpaired (G.induce (↑U : Set V)) (under U H) (under U D) n
  minimal : sys.Minimal

namespace Second
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {U H D : Finset V} {n : ℕ}

noncomputable def record (Q : Second G U H D n) : System G :=
  System.ofMinimal U (fun i => (Q.sys.segment i).left.val) (under U D)
    Q.sys.routing (Unpaired.routing_minimal Q.minimal)

def source (Q : Second G U H D n) (i : Fin n) : V := (Q.sys.segment i).left.val.val

def target (Q : Second G U H D n) (i : Fin n) : ↥D :=
  ⟨(Q.sys.segment i).walk.1.val,(mem_under _).mp (Q.sys.segment i).right_mem⟩

noncomputable def route (Q : Second G U H D n) (i : Fin n) :
    G.Path (Q.source i) (Q.target i).val :=
  ⟨(Q.sys.segment i).walk.2.val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩,
    (Q.sys.segment i).walk.2.property.map Subtype.val_injective⟩

lemma mem_route (Q : Second G U H D n) (i : Fin n) (v : V) :
    v∈(Q.route i).val.support ↔
    ∃ w : ↥(↑U : Set V), w∈(Q.sys.segment i).walk.2.val.support ∧ w.val=v := by
  change v∈((Q.sys.segment i).walk.2.val.map
    ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support ↔ _
  rw [Walk.support_map,List.mem_map]
  rfl

lemma source_mem (Q : Second G U H D n) (i : Fin n) : Q.source i∈H :=
  (mem_under _).mp (Q.sys.segment i).left.property

lemma source_injective (Q : Second G U H D n) : Function.Injective Q.source := by
  intro i j he
  exact Q.sys.source_injective (Subtype.ext (Subtype.ext he))

lemma route_domain (Q : Second G U H D n) (i : Fin n) {v : V}
    (hv : v∈(Q.route i).val.support) : v∈U := by
  obtain ⟨w,_,rfl⟩ := (Q.mem_route i v).mp hv
  exact w.property

lemma source_only (Q : Second G U H D n) (i : Fin n) (v : V)
    (hv : v∈(Q.route i).val.support) (hH : v∈H) : v=Q.source i := by
  obtain ⟨w,hw,rfl⟩ := (Q.mem_route i v).mp hv
  exact congrArg Subtype.val (Q.minimal.source_only i w hw ((mem_under _).mpr hH))

lemma target_only (Q : Second G U H D n) (i : Fin n) (v : V)
    (hv : v∈(Q.route i).val.support) (hD : v∈D) : v=(Q.target i).val := by
  obtain ⟨w,hw,rfl⟩ := (Q.mem_route i v).mp hv
  exact congrArg Subtype.val (Q.minimal.target_only i w hw ((mem_under _).mpr hD))

lemma disjoint (Q : Second G U H D n) (i j : Fin n) (hij : i≠j) :
    Disjoint {v | v∈(Q.route i).val.support} {v | v∈(Q.route j).val.support} := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  obtain ⟨a,ha,rfl⟩ := (Q.mem_route i v).mp hv
  obtain ⟨b,hb,he⟩ := (Q.mem_route j a.val).mp hw
  have heq : b=a := Subtype.ext he
  subst b
  exact Set.disjoint_left.mp (Q.sys.disjoint i j hij) ha hb

@[simp] lemma record_domain (Q : Second G U H D n) : Q.record.domain=U := rfl
@[simp] lemma record_count (Q : Second G U H D n) : Q.record.n=n := by
  simp only [record,System.ofMinimal,Fintype.card_fin]

lemma record_starts (Q : Second G U H D n) : Q.record.starts=univ.image Q.source :=
  System.ofMinimal_starts _ _ _ _ _

lemma record_source_injective (Q : Second G U H D n) :
    Function.Injective Q.record.source := by
  apply System.ofMinimal_injective
  intro i j he
  exact Q.sys.source_injective (Subtype.ext he)

lemma record_ends (Q : Second G U H D n) : Q.record.ends⊆D := by
  intro v hv
  have hh := System.ofMinimal_ends U _ _ Q.sys.routing (Unpaired.routing_minimal Q.minimal) hv
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hh
  exact (mem_under _).mp hw

lemma mem_record_used (Q : Second G U H D n) (v : V) :
    v∈Q.record.used ↔ ∃ i, v∈(Q.route i).val.support := by
  rw [record,System.mem_ofMinimal_used]
  simp only [Q.mem_route,Unpaired.routing]

theorem exists_in_region (U S H D : Finset V) (n : ℕ)
    (hSU : S⊆U) (hHS : H⊆S) (hDS : D⊆S)
    (hc : KConnectedOn G S n) (hH : n≤H.card) (hD : n≤D.card) :
    Nonempty (Second G U H D n) := by
  have hHU := hHS.trans hSU
  have hDU := hDS.trans hSU
  have hcardH : n≤(under U H).card := by simpa only [under_card hHU] using hH
  obtain ⟨A,hA,hAn⟩ := Finset.exists_subset_card_eq hcardH
  obtain ⟨P⟩ := packing_of_kConnectedOn (G.induce (↑U : Set V)) (under U S)
    A (under U D) (under_connected G hSU hc) (hA.trans (under_mono hHS)) (under_mono hDS)
    (by omega) (by rw [hAn,under_card hDU]; exact hD)
  let e : Fin n ≃ ↥A := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hAn)).symm
  obtain ⟨E,hE⟩ := Unpaired.exists_minimal ⟨Unpaired.ofFullPacking P hA e⟩
  exact ⟨⟨E,hE⟩⟩

end Second
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma congestion_sum {A B V : Type} [Fintype A] [Fintype B]
    (P : A → Bool → Set V) (Q : B → Bool → Set V) (v : V) :
    (univ.filter (fun ib : (A⊕B)×Bool =>
      v∈Sum.elim (fun a => P a ib.2) (fun b => Q b ib.2) ib.1)).card =
    (univ.filter (fun ib : A×Bool => v∈P ib.1 ib.2)).card +
    (univ.filter (fun ib : B×Bool => v∈Q ib.1 ib.2)).card := by
  classical
  simp only [card_eq_sum_ones,sum_filter,←univ_product_univ,sum_product]
  rw [Fintype.sum_sum_type]
  rfl

variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {Z H D : Finset V}

omit [Fintype V] in
lemma double_congestion (P : DoublePacking G Z D) (v : V) :
    (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 2 := by
  classical
  by_cases hv : v∈Z
  · apply (card_le_card (t:=({⟨v,hv⟩}×ˢuniv)) ?_).trans
      (by simp)
    intro ib hib
    have he := P.source_only ib v (mem_filter.mp hib).2 hv
    exact mem_product.mpr ⟨mem_singleton.mpr (Subtype.ext he.symm),mem_univ _⟩
  · have hc : (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hne
      have he := P.overlap i j hne v (mem_filter.mp hi).2 (mem_filter.mp hj).2
      exact hv (he.1 ▸ i.1.property)
    omega

omit [Fintype V] in
lemma double_congestion_off (P : DoublePacking G Z D) (v : V) (hv : v∉Z) :
    (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hne
  have he := P.overlap i j hne v (mem_filter.mp hi).2 (mem_filter.mp hj).2
  exact hv (he.1 ▸ i.1.property)

theorem combine_double (P : DoublePacking G Z D)
    (s : I×Bool → V) (tar : I×Bool → ↥D)
    (Q : ∀ i, G.Path (s i) (tar i).val)
    (hs : Function.Injective s) (hsH : ∀ i, s i∈H)
    (hZH : Disjoint Z H) (hZD : Disjoint Z D) (hHD : Disjoint H D)
    (hP : ∀ i v, v∈(P.route i).val.support → v∉H)
    (hQZ : ∀ i v, v∈(Q i).val.support → v∉Z)
    (hQH : ∀ i v, v∈(Q i).val.support → v∈H → v=s i)
    (hQQ : ∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support}
      {v | v∈(Q j).val.support}) :
    Nonempty (PairedSources.Packing G
      (fun (i : ↥Z⊕I) b => Sum.elim Subtype.val (fun j => s (j,b)) i) D
      {v | (∃ i, v∈(P.route i).val.support) ∨ ∃ i, v∈(Q i).val.support}) := by
  classical
  let src : (↥Z⊕I) → Bool → V :=
    fun i b => Sum.elim Subtype.val (fun j => s (j,b)) i
  let dest : (↥Z⊕I) → Bool → ↥D := fun i b =>
    Sum.elim (fun z => P.target (z,b)) (fun j => tar (j,b)) i
  let paths : ∀ i b, G.Path (src i b) (dest i b).val := fun i b =>
    match i with
    | .inl z => P.route (z,b)
    | .inr j => Q (j,b)
  apply PairedSources.combine dest paths
  · intro i b j c he
    dsimp only [src] at he
    cases i with
    | inl z =>
      cases j with
      | inl w => exact congrArg Sum.inl (Subtype.ext he)
      | inr j => exact (Finset.disjoint_left.mp hZH z.property ((show z.val = s (j,c) from he).symm ▸ hsH (j,c))).elim
    | inr i =>
      cases j with
      | inl z => exact (Finset.disjoint_left.mp hZH z.property ((show s (i,b) = z.val from he) ▸ hsH (i,b))).elim
      | inr j => exact congrArg Sum.inr (congrArg Prod.fst (hs he))
  · intro v hv i b
    cases i with
    | inl z => exact fun he => Finset.disjoint_left.mp hZD (he ▸ z.property) hv
    | inr i => exact fun he => Finset.disjoint_left.mp hHD (he ▸ hsH (i,b)) hv
  · intro i b v hv
    cases i with
    | inl z => exact Or.inl ⟨(z,b),hv⟩
    | inr i => exact Or.inr ⟨(i,b),hv⟩
  · intro i b v hv j c he
    cases i with
    | inl z =>
      cases j with
      | inl w => exact P.source_only (z,b) v hv (he ▸ w.property)
      | inr j => exact (hP (z,b) v hv (he ▸ hsH (j,c))).elim
    | inr i =>
      cases j with
      | inl w => exact (hQZ (i,b) v hv (he ▸ w.property)).elim
      | inr j => exact hQH (i,b) v hv (he ▸ hsH (j,c))
  · intro v
    have he : (univ.filter (fun ib : (↥Z⊕I)×Bool =>
        v∈(paths ib.1 ib.2).val.support)).card =
        (univ.filter (fun ib : ↥Z×Bool => v∈(P.route ib).val.support)).card +
        (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support)).card := by
      convert congestion_sum (fun a b => {v | v∈(P.route (a,b)).val.support})
        (fun a b => {v | v∈(Q (a,b)).val.support}) v using 2
      · congr 1
        funext ib
        cases ib.1 <;> rfl
      · simp only [Set.mem_ofPred_eq]
      · simp only [Set.mem_ofPred_eq]
    rw [he]
    by_cases hv : v∈Z
    · have hzero : (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support))=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hQZ i v (mem_filter.mp hi).2 hv
      rw [hzero,card_empty,Nat.add_zero]
      exact double_congestion P v
    · have hq : (univ.filter (fun ib : I×Bool => v∈(Q ib).val.support)).card≤1 := by
        apply card_le_one.mpr
        intro i hi j hj
        by_contra hne
        exact Set.disjoint_left.mp (hQQ i j hne) (mem_filter.mp hi).2 (mem_filter.mp hj).2
      have hp := double_congestion_off P v hv
      omega

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

theorem reroute_sources (J : Set V) {a b : ℕ} (hJ : WovenOn G J a b)
    (u : Fin a → V) (hu : Function.Injective u) (huJ : ∀ j, u j∈J)
    (x y : I → V) (P : ∀ i, G.Path (x i) (y i))
    (hcard : Fintype.card I ≤ b)
    (hPP : ∀ i j, i≠j → Disjoint {v | v∈(P i).val.support} {v | v∈(P j).val.support})
    (hroot : ∀ i j, u j∈(P i).val.support → u j=x i) :
    ∃ M : RootedCliqueModel G u, (∀ j, M.branch j⊆J) ∧
    ∃ Q : ∀ i, G.Path (x i) (y i),
      (∀ i j, i≠j → Disjoint {v | v∈(Q i).val.support} {v | v∈(Q j).val.support}) ∧
      (∀ i v, v∈(Q i).val.support → v∉J → v∈(P i).val.support) ∧
      (∀ i j v, v∈(Q i).val.support → v∈M.branch j → v=x i ∧ v=u j) := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨M,hMJ,Q,hQQ,_,hQP,hQM⟩ := reroute_woven_district G J hJ u hu huJ
    (x ∘ e) (y ∘ e) (fun i => P (e i)) hcard
    (fun i j hij => hPP _ _ (fun h => hij (e.injective h)))
  let Q' : ∀ i, G.Path (x i) (y i) := fun i =>
    ⟨(Q (e.symm i)).val.copy (congrArg x (e.apply_symm_apply i))
      (congrArg y (e.apply_symm_apply i)),by simp⟩
  have hsup (i : I) (v : V) : v∈(Q' i).val.support ↔ v∈(Q (e.symm i)).val.support := by
    simp [Q']
  refine ⟨M,hMJ,Q',?_,?_,?_⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro v hv hw
    exact Set.disjoint_left.mp (hQQ _ _ (fun h => hij (e.symm.injective h)))
      ((hsup i v).mp hv) ((hsup j v).mp hw)
  · intro i v hv hvJ
    have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
    exact he ▸ hQP _ v ((hsup i v).mp hv) hvJ
  · intro i j v hv hvm
    obtain ⟨⟨j',rfl⟩,D,hD⟩ := hQM _ j v ((hsup i v).mp hv) hvm
    have horig : u j'∈(P i).val.support := by
      have he := congrArg (fun j => (P j).val.support) (e.apply_symm_apply i)
      rw [←he]
      rcases hD with hd | hd
      · exact hd.symm ▸ D.entry_on
      · exact hd.symm ▸ D.exit_on
    have he := hroot i j' horig
    have hj : j'=j := by
      by_contra hne
      exact Set.disjoint_left.mp (M.disjoint j' j hne) (M.root_mem j') hvm
    exact ⟨he,congrArg u hj⟩

omit [DecidableEq V] in

lemma retain_endpoint {J A : Set V} (hJA : Disjoint J A)
    {x y : V} (P Q : G.Path x y)
    (hQP : ∀ v, v∈Q.val.support → v∉J → v∈P.val.support)
    (hPA : ∀ v, v∈P.val.support → v∈A → v=x) :
    ∀ v, v∈Q.val.support → v∈A → v=x := by
  intro v hv hvA
  exact hPA v (hQP v hv (fun hvJ => Set.disjoint_left.mp hJA hvJ hvA)) hvA

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

abbrev Roles (t a : ℕ) := Fin t ⊕ (Fin a ⊕ Fin t)

def roleOwner {t a : ℕ} (label : Fin a → Fin t) : Roles t a → Fin t :=
  Sum.elim id (Sum.elim label id)

def roleStart {V : Type} {t a : ℕ} (w : Fin t → V) (u : Fin a → V)
    (w' : Fin t → V) : Roles t a → V := Sum.elim w (Sum.elim u w')

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [DecidableEq V] {t a : ℕ}

noncomputable def oldSources (w : Fin t → V) (u : Fin a → V) : Finset V :=
  univ.image w ∪ univ.image u

@[simp] lemma mem_oldSources (w : Fin t → V) (u : Fin a → V) (v : V) :
    v∈oldSources w u ↔ (∃ i, w i=v) ∨ ∃ j, u j=v := by
  simp [oldSources]

noncomputable def roleTo (w : Fin t → V) (u : Fin a → V) : Roles t a → (↥(oldSources w u)⊕Fin t)
  | .inl i => .inl ⟨w i,(mem_oldSources w u _).mpr (Or.inl ⟨i,rfl⟩)⟩
  | .inr (.inl j) => .inl ⟨u j,(mem_oldSources w u _).mpr (Or.inr ⟨j,rfl⟩)⟩
  | .inr (.inr i) => .inr i

lemma roleTo_bijective (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j) :
    Function.Bijective (roleTo w u) := by
  constructor
  · rintro (i|j|i) (i'|j'|i') he
    · exact congrArg Sum.inl (hw (congrArg Subtype.val (Sum.inl.inj he)))
    · exact (hwu i j' (congrArg Subtype.val (Sum.inl.inj he))).elim
    · cases he
    · exact (hwu i' j (congrArg Subtype.val (Sum.inl.inj he)).symm).elim
    · exact congrArg (Sum.inr ∘ Sum.inl) (hu (congrArg Subtype.val (Sum.inl.inj he)))
    · cases he
    · cases he
    · cases he
    · exact congrArg (Sum.inr ∘ Sum.inr) (Sum.inr.inj he)
  · rintro (z|i)
    · rcases (mem_oldSources w u z.val).mp z.property with ⟨i,hi⟩|⟨j,hj⟩
      · exact ⟨Sum.inl i,congrArg Sum.inl (Subtype.ext hi)⟩
      · exact ⟨Sum.inr (Sum.inl j),congrArg Sum.inl (Subtype.ext hj)⟩
    · exact ⟨Sum.inr (Sum.inr i),rfl⟩

noncomputable def roleEquiv (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j) :
    Roles t a ≃ (↥(oldSources w u)⊕Fin t) := Equiv.ofBijective _ (roleTo_bijective w u hw hu hwu)

end LinearListHadwiger.Stage

namespace LinearListHadwiger.PairedSources.Packing
open SimpleGraph Finset
variable {V I : Type} {G : SimpleGraph V} {s : I → Bool → V} {D : Finset V} {U : Set V}

lemma target_injective (P : PairedSources.Packing G s D U) : Function.Injective P.target := by
  intro i j he
  by_contra hij
  exact Set.disjoint_left.mp (P.disjoint i j hij) (P.route i).val.end_mem_support
    (Eq.mpr (congrArg (fun v => v∈(P.route j).val.support) (congrArg Subtype.val he))
      (P.route j).val.end_mem_support)

lemma source_injective (P : PairedSources.Packing G s D U) :
    Function.Injective (fun i => s i (P.choose i)) := by
  intro i j he
  by_contra hij
  exact Set.disjoint_left.mp (P.disjoint i j hij) (P.route i).val.start_mem_support
    (Eq.mpr (congrArg (fun v => v∈(P.route j).val.support) he)
      (P.route j).val.start_mem_support)

end LinearListHadwiger.PairedSources.Packing

end OAI
