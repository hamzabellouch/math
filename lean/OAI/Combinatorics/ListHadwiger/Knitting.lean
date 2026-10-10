import OAI.Combinatorics.ListHadwiger.Assembly

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma connected_induce_congr {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {S T : Finset V} (h : S = T)
    (hc : (G.induce (↑S : Set V)).Connected) :
    (G.induce (↑T : Set V)).Connected := h ▸ hc

lemma delete_connected (G : SimpleGraph V) {S Z : Finset V} {k : ℕ}
    (hc : KConnectedOn G S k) (hZ : Z ⊆ S) (hz : Z.card < k) :
    KConnectedOn G (S \ Z) (k-Z.card) := by
  classical
  refine ⟨?_,?_⟩
  · have hs := Finset.card_sdiff_add_card_eq_card hZ
    have := hc.1
    omega
  · intro X hX hx
    have hXZ : Disjoint X Z := Finset.disjoint_left.mpr (fun v hv hz =>
      (Finset.mem_sdiff.mp (hX hv)).2 hz)
    have huS : Z ∪ X ⊆ S := Finset.union_subset hZ
      (hX.trans Finset.sdiff_subset)
    have huc : (Z ∪ X).card < k := by
      rw [Finset.card_union_of_disjoint hXZ.symm]
      omega
    apply connected_induce_congr G (show S \ (Z ∪ X) = (S \ Z) \ X by
      ext v; simp only [Finset.mem_sdiff,Finset.mem_union]; tauto)
    exact hc.2 _ huS huc

theorem packing_from_many_neighbors {I : Type} [Fintype I]
    (G : SimpleGraph V) (A B : Finset V) (C : I → Set V) (s : I → V)
    (N : I → Finset V) (c : ℕ) (hc : 0 < c)
    (hs : ∀ i, s i ∈ A) (hsC : ∀ i, s i ∈ C i)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hN : ∀ i, N i ⊆ B) (hcard : ∀ i, A.card ≤ (N i).card)
    (hadj : ∀ i b, b ∈ N i → ∃ w ∈ C i, G.Adj w b)
    (hcon : ∀ v, (Finset.univ.filter fun i => v ∈ C i).card ≤ c)
    (hI : c * A.card ≤ Fintype.card I) : Nonempty (FullPacking G A B) := by
  classical
  apply fullPacking_of_no_small_separator
  intro X hX
  obtain ⟨i,hi⟩ := exists_region_avoiding C X c A.card hc hI hX (fun v _ => hcon v)
  have hn : ¬N i ⊆ X := fun h => (Nat.not_le_of_lt (hX.trans_le (hcard i)))
    (Finset.card_le_card h)
  simp only [Finset.subset_iff,not_forall] at hn
  obtain ⟨b,hb,hbX⟩ := hn
  obtain ⟨w,hw,hwb⟩ := hadj i b hb
  obtain ⟨p⟩ := (hC i).preconnected ⟨s i,hsC i⟩ ⟨w,hw⟩
  let q : G.Walk (s i) w := p.map (Embedding.induce (C i)).toHom
  refine ⟨s i,hs i,b,hN i hb,q.append hwb.toWalk,?_⟩
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · have hv' : v ∈ (p.map (Embedding.induce (C i)).toHom).support := hv
    rw [Walk.support_map] at hv'
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hv'
    exact hi z.val z.property
  · have hv' : v = w ∨ v = b := by simpa using hv
    rcases hv' with rfl | rfl
    · exact hi _ hw
    · exact hbX

theorem short_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : G.Connected) {k : ℕ} (hk : 0 < k)
    (hdeg : ∀ v, k ≤ (Density.neighbors G Finset.univ v).card) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length < 3 * (Fintype.card V / k + 1) := by
  classical
  obtain ⟨p,hp⟩ := hc.exists_walk_length_eq_dist u v
  let n := p.length / 3 + 1
  let N (i : Fin n) := Density.neighbors G Finset.univ (p.getVert (3*i.val))
  have hidx : ∀ i : Fin n, 3*i.val ≤ p.length := by
    intro i
    have := i.isLt
    dsimp [n] at this
    have := Nat.mod_add_div p.length 3
    omega
  have hdist : ∀ i : Fin n, G.dist u (p.getVert (3*i.val)) = 3*i.val := by
    intro i
    have h := length_eq_dist_of_subwalk hp (p.isSubwalk_take (3*i.val))
    simpa [Walk.take_length, Nat.min_eq_left (hidx i)] using h.symm
  have hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (N i) (N j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hi : G.Adj (p.getVert (3*i.val)) w := (Density.mem_neighbors G).mp hwi |>.2
    have hj : G.Adj (p.getVert (3*j.val)) w := (Density.mem_neighbors G).mp hwj |>.2
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert (3*i.val)) (w := w)
    have h₂ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*j.val))
    have h₃ := hc.dist_triangle (u := u) (v := p.getVert (3*j.val)) (w := w)
    have h₄ := hc.dist_triangle (u := u) (v := w) (w := p.getVert (3*i.val))
    rw [hdist i, dist_eq_one_iff_adj.mpr hi] at h₁
    rw [hdist j, dist_eq_one_iff_adj.mpr hj.symm] at h₂
    rw [hdist j, dist_eq_one_iff_adj.mpr hj] at h₃
    rw [hdist i, dist_eq_one_iff_adj.mpr hi.symm] at h₄
    have he : i.val = j.val := by omega
    exact hij (Fin.ext he)
  have hsum : (∑ i : Fin n, (N i).card) ≤ Fintype.card V := by
    rw [← Finset.card_biUnion (s := Finset.univ) (t := N)]
    · exact Finset.card_le_univ _
    · intro i _ j _ hij
      exact hdisj i j hij
  have hnk : n*k ≤ Fintype.card V := by
    calc
      n*k = ∑ i : Fin n, k := by simp
      _ ≤ ∑ i : Fin n, (N i).card := Finset.sum_le_sum (fun i _ => hdeg _)
      _ ≤ Fintype.card V := hsum
  have hn : n ≤ Fintype.card V / k := (Nat.le_div_iff_mul_le hk).mpr hnk
  refine ⟨p,p.isPath_of_length_eq_dist hp,?_⟩
  have := Nat.mod_lt p.length (by omega : 0 < 3)
  have := Nat.mod_add_div p.length 3
  dsimp [n] at hn
  omega

lemma min_degree {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset V} {k : ℕ} (hc : KConnectedOn G S k) {u : V} (hu : u ∈ S) :
    k ≤ (Density.neighbors G S u).card := by
  classical
  by_contra hn
  have hn : (Density.neighbors G S u).card < k := by omega
  let N := Density.neighbors G S u
  have hNS : N ⊆ S := Finset.filter_subset _ _
  have huN : u ∉ N := by simp [N,Density.neighbors]
  have huR : u ∈ S \ N := Finset.mem_sdiff.mpr ⟨hu,huN⟩
  have hnot : ¬S \ N ⊆ {u} := by
    intro h
    have hh := Finset.card_le_card h
    have he := Finset.card_sdiff_add_card_eq_card hNS
    have hs := hc.1
    simp only [Finset.card_singleton] at hh
    dsimp [N] at he hh
    omega
  simp only [Finset.subset_iff,not_forall,Finset.mem_singleton] at hnot
  obtain ⟨v,hv,hvu⟩ := hnot
  obtain ⟨p⟩ := (hc.2 N hNS hn).preconnected ⟨u,huR⟩ ⟨v,hv⟩
  have hp : ¬p.Nil := p.not_nil_of_ne (fun h => hvu (congrArg Subtype.val h).symm)
  have ha : G.Adj u p.snd.val := p.adj_snd hp
  exact (Finset.mem_sdiff.mp p.snd.property).2
    (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp p.snd.property).1,ha⟩)

lemma induce_connected {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) :
    KConnectedOn (G.induce (↑S : Set V)) Finset.univ k := by
  classical
  refine ⟨by simpa using hc.1,?_⟩
  intro X _ hx
  let Z := X.image Subtype.val
  have hZ : Z ⊆ S := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.property
  have hZk : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ Subtype.val_injective] using hx
  have hconn := hc.2 Z hZ hZk
  let f : G.induce (↑(S \ Z) : Set V) →g
      (G.induce (↑S : Set V)).induce (↑(Finset.univ \ X) : Set ↥S) :=
    { toFun := fun v => ⟨⟨v.val,(Finset.mem_sdiff.mp v.property).1⟩,
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hv =>
          (Finset.mem_sdiff.mp v.property).2 (Finset.mem_image.mpr ⟨_,hv,rfl⟩)⟩⟩
      map_rel' := by intro u v h; exact h }
  apply hconn.map f
  intro w
  have hw : w.val.val ∈ S \ Z := by
    refine Finset.mem_sdiff.mpr ⟨w.val.property,?_⟩
    intro hz
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
    have heq : a = w.val := Subtype.ext he
    exact (Finset.mem_sdiff.mp w.property).2 (heq ▸ ha)
  exact ⟨⟨w.val.val,hw⟩,rfl⟩

lemma connected_of_kConnected (G : SimpleGraph V) {S : Finset V} {k : ℕ}
    (hc : KConnectedOn G S k) (hk : 0 < k) : (G.induce (↑S : Set V)).Connected := by
  exact connected_induce_congr G (Finset.sdiff_empty (s := S))
    (hc.2 ∅ (Finset.empty_subset _) (by simpa using hk))

theorem short_avoiding_path (G : SimpleGraph V) (S X : Finset V) {k : ℕ}
    (hc : KConnectedOn G S k) (hXS : X ⊆ S) (hX : X.card < k)
    {u v : V} (hu : u ∈ S \ X) (hv : v ∈ S \ X) :
    ∃ p : G.Walk u v, p.IsPath ∧
      p.length < 3 * (S.card / (k-X.card) + 1) ∧
      ∀ w ∈ p.support, w ∈ S \ X := by
  classical
  let R := S \ X
  let H := G.induce (↑R : Set V)
  have hr := delete_connected G hc hXS hX
  have hr' := induce_connected G R hr
  have hhk : 0 < k-X.card := by omega
  have hconn : H.Connected := by
    have hhh := connected_of_kConnected G hr hhk
    exact hhh
  obtain ⟨p,hp,hl⟩ := short_path H hconn hhk (fun w => min_degree H hr' (Finset.mem_univ w))
    (⟨u,hu⟩ : R) (⟨v,hv⟩ : R)
  let q : G.Walk u v := p.map (Embedding.induce (↑R : Set V)).toHom
  refine ⟨q,hp.map (f := (Embedding.induce (G := G) (↑R : Set V)).toHom) Subtype.val_injective,?_,?_⟩
  · have hcard : Fintype.card ↥R ≤ S.card := by
      simpa using Finset.card_le_card (Finset.sdiff_subset : R ⊆ S)
    have hdiv : Fintype.card ↥R / (k-X.card) ≤ S.card / (k-X.card) := Nat.div_le_div_right hcard
    change (p.map (Embedding.induce (G := G) (↑R : Set V)).toHom).length < _
    rw [Walk.length_map]
    exact hl.trans_le (by omega :
      3*(Fintype.card ↥R / (k-X.card)+1) ≤ 3*(S.card/(k-X.card)+1))
  · intro w hw
    change w ∈ (p.map (Embedding.induce (G := G) (↑R : Set V)).toHom).support at hw
    rw [Walk.support_map] at hw
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw
    exact z.property

def packedBranch {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : Set V :=
  {b.val} ∪ {v | ∃ a, P.target a = b ∧ v ∈ (P.route a).val.support}

lemma packedBranch_target {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : b.val ∈ packedBranch P b := Or.inl rfl

lemma packedBranch_source {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (a : ↥A) : a.val ∈ packedBranch P (P.target a) :=
  Or.inr ⟨a,rfl,(P.route a).val.start_mem_support⟩

lemma packedBranch_connected {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : (G.induce (packedBranch P b)).Connected := by
  classical
  by_cases hh : ∃ a, P.target a = b
  · obtain ⟨a,rfl⟩ := hh
    have he : packedBranch P (P.target a) = {v | v ∈ (P.route a).val.support} := by
      ext v
      constructor
      · rintro (rfl | ⟨a',ha',hv⟩)
        · exact (P.route a).val.end_mem_support
        · have heq := P.target_injective ha'
          cases heq
          exact hv
      · exact fun hv => Or.inr ⟨a,rfl,hv⟩
    rw [he]
    exact (P.route a).val.connected_induce_support
  · have he : packedBranch P b = {b.val} := by
      ext v
      constructor
      · rintro (hv | ⟨a,ha,_⟩)
        · exact hv
        · exact (hh ⟨a,ha⟩).elim
      · exact Or.inl
    rw [he]
    exact SimpleGraph.Connected.of_subsingleton

lemma packedBranch_disjoint {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b c : ↥B) (hbc : b ≠ c) :
    Disjoint (packedBranch P b) (packedBranch P c) := by
  apply Set.disjoint_left.mpr
  intro v hv hv'
  rcases hv with hv | ⟨a,ha,hva⟩ <;> rcases hv' with hv' | ⟨a',ha',hva'⟩
  · exact hbc (Subtype.ext (hv.symm.trans hv'))
  · have ht := P.target_only a' v hva' (hv ▸ b.property)
    exact hbc (Subtype.ext (hv.symm.trans (ht.trans (congrArg Subtype.val ha'))))
  · have ht := P.target_only a v hva (hv' ▸ c.property)
    exact hbc (Subtype.ext ((congrArg Subtype.val ha).symm.trans (ht.symm.trans hv')))
  · have hne : a ≠ a' := by
      rintro rfl
      exact hbc (ha.symm.trans ha')
    exact Set.disjoint_left.mp (P.disjoint a a' hne) hva hva'

noncomputable def absorb_packing {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) : MinorModel G (G.induce (↑B : Set V)) where
  branch := packedBranch P
  connected := packedBranch_connected P
  disjoint := packedBranch_disjoint P
  adjacent := by
    intro b c hbc
    exact ⟨b.val,packedBranch_target P b,c.val,packedBranch_target P c,hbc⟩

def compose_model {W U : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph U} (M : MinorModel G H) (N : MinorModel H K) : MinorModel G K where
  branch u := M.expand (N.branch u)
  connected u := M.expand_connected (N.connected u)
  disjoint u v huv := M.expand_disjoint (N.disjoint u v huv)
  adjacent := by
    intro u v huv
    obtain ⟨a,ha,b,hb,hab⟩ := N.adjacent huv
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent hab
    exact ⟨x,⟨a,ha,hx⟩,y,⟨b,hb,hy⟩,hxy⟩

theorem root_minor_core {J : Type} [Fintype J] [DecidableEq J]
    (G : SimpleGraph V) (H : SimpleGraph J) [DecidableRel H.Adj]
    (A : Finset V) (M : MinorModel G H)
    (hc : KConnectedOn G Finset.univ (2*A.card))
    (haB : ∀ j, Disjoint (↑A : Set V) (M.branch j))
    (hdeg : ∀ j, 3*A.card ≤ (Density.neighbors H Finset.univ j).card)
    (hsize : 3*A.card ≤ Fintype.card J) :
    ∃ T : Finset J, Fintype.card J ≤ T.card + 2*A.card ∧
      ∃ N : MinorModel G (H.induce (↑T : Set J)),
      ∃ f : ↥A → ↥T, Function.Injective f ∧ ∀ a, a.val ∈ N.branch (f a) := by
  classical
  let B := M.branch
  obtain ⟨D,hD⟩ := BagRouting.exists_avoiding_unused M.disjoint
    (bagRouting_of_double_packing G A B hc M.connected M.disjoint haB (by omega))
  let Used := Finset.univ.image D.bag
  let T : Finset J := Finset.univ \ Used
  have hUsed : Used.card = 2*A.card := by
    simp [Used,Finset.card_image_of_injective _ D.bag_injective,Nat.mul_comm]
  have hTcard : Fintype.card J = T.card+2*A.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Used)
    simpa only [Finset.card_univ,hUsed] using h.symm
  have hunused : ∀ j : ↥T, j.val ∉ Set.range D.bag := by
    intro j ⟨i,hi⟩
    exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
  let BT : ↥T → Set V := fun j => B j.val
  let W := BagContraction.Vertex BT
  let Q := BagContraction.graph G BT
  have hreg : ∀ i : ↥A × Bool, D.region i ⊆ BagContraction.Remnant BT := by
    intro i v hv j hvj
    exact Set.disjoint_left.mp (D.region_avoids_unused M.disjoint hD j.val (hunused j) i) hv hvj
  have harem : ∀ a : ↥A, a.val ∈ BagContraction.Remnant BT := by
    intro a j hj
    exact Set.disjoint_left.mp (haB j.val) a.property hj
  let src : ↥A → W := fun a => .inl ⟨a.val,harem a⟩
  have hsrc : Function.Injective src := by
    intro a b hab
    have hh : (⟨a.val,harem a⟩ : ↥(BagContraction.Remnant BT)) = ⟨b.val,harem b⟩ := Sum.inl.inj hab
    exact Subtype.ext (congrArg (fun z : ↥(BagContraction.Remnant BT) => z.val) hh)
  let AS : Finset W := Finset.univ.image src
  let TS : Finset W := Finset.univ.image (Sum.inr : ↥T → W)
  have hAS : AS.card = A.card := by simp [AS,Finset.card_image_of_injective _ hsrc]
  let C := fun i : ↥A × Bool => BagContraction.liftSet BT (D.region i)
  have hcon : ∀ w : W, (Finset.univ.filter fun i => w ∈ C i).card ≤ 2 := by
    intro w
    cases w with
    | inl v => exact D.region_congestion M.disjoint haB v.val
    | inr j =>
      have he : (Finset.univ.filter fun i => (Sum.inr j : W) ∈ C i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      rw [he]
      simp
  let Nbr (i : ↥A × Bool) : Finset ↥T := Finset.univ.filter fun j => H.Adj (D.bag i) j.val
  let NT (i : ↥A × Bool) : Finset W := (Nbr i).image Sum.inr
  have hNT : ∀ i, AS.card ≤ (NT i).card := by
    intro i
    have hcount : (Nbr i).card = ((Density.neighbors H Finset.univ (D.bag i)) \ Used).card := by
      have he : (Nbr i).image Subtype.val = (Density.neighbors H Finset.univ (D.bag i)) \ Used := by
        ext j
        simp only [Nbr,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
          Density.mem_neighbors,Finset.mem_sdiff]
        constructor
        · rintro ⟨w,hw,rfl⟩
          exact ⟨hw,(Finset.mem_sdiff.mp w.property).2⟩
        · rintro ⟨hj,hju⟩
          exact ⟨⟨j,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hju⟩⟩,hj,rfl⟩
      rw [← he,Finset.card_image_of_injective _ Subtype.val_injective]
    have hsplit := Finset.card_sdiff_add_card_inter (Density.neighbors H Finset.univ (D.bag i)) Used
    have hInt := Finset.card_le_card (Finset.inter_subset_right :
      Density.neighbors H Finset.univ (D.bag i) ∩ Used ⊆ Used)
    have hd := hdeg (D.bag i)
    rw [hUsed] at hInt
    rw [← hcount] at hsplit
    rw [hAS]
    dsimp [NT]
    rw [Finset.card_image_of_injective _ Sum.inr_injective]
    omega
  have hadj : ∀ i b, b ∈ NT i → ∃ w ∈ C i, Q.Adj w b := by
    intro i b hb
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hb
    apply BagContraction.liftSet_adj_target G BT (hreg i)
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent (Finset.mem_filter.mp hj).2
    exact ⟨x,Or.inr hx,y,hy,hxy⟩
  obtain ⟨P⟩ := packing_from_many_neighbors Q AS TS C (fun i => src i.1) NT 2 (by omega)
    (fun i => Finset.mem_image.mpr ⟨i.1,Finset.mem_univ _,rfl⟩)
    (fun i => D.root_mem_region i)
    (fun i => BagContraction.liftSet_connected G BT (hreg i) (D.region_connected M.connected i))
    (fun i => Finset.image_subset_image (Finset.subset_univ _)) hNT hadj hcon
    (by simp [hAS,Fintype.card_prod,Nat.mul_comm])
  let MQ := BagContraction.model G BT (fun j => M.connected j.val)
    (fun i j hij => M.disjoint i.val j.val (fun h => hij (Subtype.ext h)))
  let MP := compose_model MQ (absorb_packing P)
  let fT : ↥T → ↥TS := fun j => ⟨.inr j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩
  have hfT : Function.Bijective fT := by
    constructor
    · intro i j hij
      exact Sum.inr_injective (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext hi⟩
  let e := Equiv.ofBijective fT hfT
  let N : MinorModel G (H.induce (↑T : Set J)) :=
    { branch := fun j => MP.branch (e j)
      connected := fun j => MP.connected (e j)
      disjoint := fun i j hij => MP.disjoint (e i) (e j) (fun h => hij (e.injective h))
      adjacent := by
        intro i j hij
        apply MP.adjacent
        change Q.Adj (.inr i) (.inr j)
        refine ⟨?_,?_⟩
        · intro h
          exact hij.ne (Sum.inr.inj h)
        · exact M.adjacent hij }
  let sA : ↥A → ↥AS := fun a => ⟨src a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  let f : ↥A → ↥T := fun a => e.symm (P.target (sA a))
  refine ⟨T,hTcard.le,N,f,?_,?_⟩
  · intro a b hab
    have he : P.target (sA a) = P.target (sA b) := e.symm.injective hab
    exact hsrc (congrArg Subtype.val (P.target_injective he))
  · intro a
    change a.val ∈ MP.branch (e (e.symm (P.target (sA a))))
    rw [e.apply_symm_apply]
    exact ⟨src a,packedBranch_source P (sA a),rfl⟩

theorem group_small_core {I : Type} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (A : Finset V) (label : ↥A → I)
    (hsurj : Function.Surjective label) (hA : 1 ≤ A.card)
    (r k : ℕ) (hc : KConnectedOn G Finset.univ k)
    (horder : Fintype.card V ≤ r*k) (hk : (12*r+18)*A.card ≤ k) :
    ∃ B : I → Finset V,
      (∀ i, (G.induce (↑(B i) : Set V)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ a : ↥A, a.val ∈ B (label a)) := by
  classical
  have hI : Fintype.card I ≤ A.card := by
    simpa using Fintype.card_le_of_surjective label hsurj
  choose rep hrep using hsurj
  let d := 6*r+6
  have hex : ∀ S : Finset ↥A, ∃ B : I → Finset V,
      (∀ i, (G.induce (↑(B i) : Set V)).Connected) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ i (a : ↥A), a.val ∈ B i → label a = i) ∧
      (∀ i, (rep i).val ∈ B i) ∧
      (∀ a ∈ S, a.val ∈ B (label a)) ∧
      (∑ i, (B i).card) ≤ Fintype.card I + d*S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun i => {(rep i).val},?_,?_,?_,?_,?_,?_⟩
      · intro i
        have : Nonempty (↑({(rep i).val} : Finset V) : Set V) := ⟨⟨(rep i).val,by simp⟩⟩
        have : Subsingleton (↑({(rep i).val} : Finset V) : Set V) := ⟨by
          intro a b
          apply Subtype.ext
          exact (Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm⟩
        exact SimpleGraph.Connected.of_subsingleton
      · intro i j hij
        apply Finset.disjoint_left.mpr
        intro v hi hj
        have he : rep i = rep j := Subtype.ext ((Finset.mem_singleton.mp hi).symm.trans (Finset.mem_singleton.mp hj))
        exact hij ((hrep i).symm.trans ((congrArg label he).trans (hrep j)))
      · intro i a ha
        have he : a = rep i := Subtype.ext (Finset.mem_singleton.mp ha)
        simpa only [he] using hrep i
      · intro i
        exact Finset.mem_singleton_self _
      · simp
      · simp
    | @insert a S ha ih =>
      obtain ⟨B,hBc,hBd,hBpure,hBr,hBS,hBcard⟩ := ih
      let i := label a
      let u := (rep i).val
      let v := a.val
      let Z := ((Finset.univ.filter (· ≠ i)).biUnion B) ∪ (A \ {u,v})
      have hS : S.card ≤ A.card := by simpa using Finset.card_le_univ S
      have hsum : (∑ j, (B j).card) ≤ (d+1)*A.card := by
        have hm := Nat.mul_le_mul_left d hS
        nlinarith
      have hZc : Z.card ≤ (d+2)*A.card := by
        have hz₁ : ((Finset.univ.filter (· ≠ i)).biUnion B).card ≤ ∑ j, (B j).card :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (by intros; omega))
        have hz₂ : (A \ {u,v}).card ≤ A.card := Finset.card_le_card Finset.sdiff_subset
        have hz := Finset.card_union_le ((Finset.univ.filter (· ≠ i)).biUnion B) (A \ {u,v})
        dsimp [Z]
        nlinarith
      have hZk : 2*Z.card < k := by dsimp [d] at hZc; nlinarith
      have huZ : u ∉ Z := by
        intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j,hj,huj⟩ := Finset.mem_biUnion.mp hz
          have hp := hBpure j (rep i) huj
          exact (Finset.mem_filter.mp hj).2 (hp.symm.trans (hrep i))
        · exact (Finset.mem_sdiff.mp hz).2 (by simp [u])
      have hvZ : v ∉ Z := by
        intro hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hz
          have hp := hBpure j a hvj
          exact (Finset.mem_filter.mp hj).2 hp.symm
        · exact (Finset.mem_sdiff.mp hz).2 (by simp [v])
      obtain ⟨p,hpath,hlen,hps⟩ := short_avoiding_path G Finset.univ Z hc
        (Finset.subset_univ _) (by omega : Z.card < k)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u,huZ⟩)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,hvZ⟩)
      have hden : 0 < k-Z.card := by omega
      have hkden : k ≤ 2*(k-Z.card) := by omega
      have hn : Fintype.card V < (2*r+1)*(k-Z.card) := by
        have hh := Nat.mul_le_mul_left r hkden
        nlinarith
      have hdiv : Fintype.card V / (k-Z.card) < 2*r+1 :=
        (Nat.div_lt_iff_lt_mul hden).mpr (by nlinarith)
      have hlen' : p.length < d := by
        rw [Finset.card_univ] at hlen
        dsimp [d]
        omega
      let P := p.support.toFinset
      have hPc : P.card ≤ d := by
        have hh := List.toFinset_card_le p.support
        rw [Walk.length_support] at hh
        dsimp [P]
        omega
      have hpZ : ∀ w ∈ P, w ∉ Z := by
        intro w hw
        exact (Finset.mem_sdiff.mp (hps w (List.mem_toFinset.mp hw))).2
      have huP : u ∈ P := List.mem_toFinset.mpr p.start_mem_support
      have hvP : v ∈ P := List.mem_toFinset.mpr p.end_mem_support
      let B' : I → Finset V := fun j => if j = i then B j ∪ P else B j
      have hBB : ∀ j, B j ⊆ B' j := by
        intro j
        by_cases hj : j=i
        · simp only [B',ite_eq_left hj]
          exact Finset.subset_union_left
        · simp only [B',ite_eq_right hj]
          exact Finset.Subset.refl _
      have hPother : ∀ j, j ≠ i → Disjoint P (B j) := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro w hw hwj
        exact hpZ w hw (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,hwj⟩))
      refine ⟨B',?_,?_,?_,?_,?_,?_⟩
      · intro j
        by_cases hj : j=i
        · subst j
          change (G.induce (↑(if i=i then B i ∪ P else B i) : Set V)).Connected
          rw [ite_eq_left rfl,Finset.coe_union]
          have hpcon : (G.induce (↑P : Set V)).Connected := by
            have he : (↑P : Set V) = {w | w ∈ p.support} := by ext w; simp [P]
            rw [he]
            exact p.connected_induce_support
          exact SimpleGraph.induce_union_connected (hBc i).preconnected hpcon.preconnected
            ⟨u,hBr i,huP⟩
        · change (G.induce (↑(if j=i then B j ∪ P else B j) : Set V)).Connected
          rw [ite_eq_right hj]
          exact hBc j
      · intro j l hjl
        by_cases hj : j=i <;> by_cases hl : l=i
        · exact (hjl (hj.trans hl.symm)).elim
        · simp only [B',ite_eq_left hj,ite_eq_right hl]
          exact Finset.disjoint_union_left.mpr ⟨hBd j l hjl,hPother l hl⟩
        · simp only [B',ite_eq_right hj,ite_eq_left hl]
          exact Finset.disjoint_union_right.mpr ⟨hBd j l hjl,(hPother j hj).symm⟩
        · simpa only [B',ite_eq_right hj,ite_eq_right hl] using hBd j l hjl
      · intro j b hb
        by_cases hj : j=i
        · change b.val ∈ if j=i then B j ∪ P else B j at hb
          rw [ite_eq_left hj] at hb
          rcases Finset.mem_union.mp hb with hb | hb
          · exact hBpure j b hb
          · have hbuv : b.val ∈ ({u,v} : Finset V) := by
              by_contra hn
              exact hpZ b.val hb (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨b.property,hn⟩))
            rcases Finset.mem_insert.mp hbuv with hbu | hbv
            · have he : b = rep i := Subtype.ext hbu
              exact (congrArg label he).trans ((hrep i).trans hj.symm)
            · have he : b = a := Subtype.ext (Finset.mem_singleton.mp hbv)
              exact (congrArg label he).trans hj.symm
        · exact hBpure j b (by simpa only [B',ite_eq_right hj] using hb)
      · intro j
        exact hBB j (hBr j)
      · intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · change v ∈ if i=i then B i ∪ P else B i
          rw [ite_eq_left rfl]
          exact Finset.mem_union_right _ hvP
        · exact hBB _ (hBS b hb)
      · have hstep : (∑ j, (B' j).card) ≤ (∑ j, (B j).card) + d := by
          calc
            (∑ j, (B' j).card) ≤ ∑ j, ((B j).card + if j=i then d else 0) := by
              apply Finset.sum_le_sum
              intro j _
              by_cases hj : j=i
              · simp only [B',ite_eq_left hj]
                exact (Finset.card_union_le _ _).trans (by omega)
              · simp [B',hj]
            _ = (∑ j, (B j).card)+d := by simp [Finset.sum_add_distrib]
        rw [Finset.card_insert_of_notMem ha]
        nlinarith
  obtain ⟨B,hcB,hdB,_,_,hAll,_⟩ := hex Finset.univ
  exact ⟨B,hcB,hdB,fun a => hAll a (Finset.mem_univ _)⟩

end LinearListHadwiger.Knitting

end OAI
