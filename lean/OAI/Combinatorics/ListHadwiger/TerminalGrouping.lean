import OAI.Combinatorics.ListHadwiger.Knitting

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def density (G : SimpleGraph V) : ℚ :=
  (G.edgeFinset.card : ℚ) / Fintype.card V

lemma model_card_le {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (M : MinorModel G H) : Fintype.card W ≤ Fintype.card V := by
  classical
  let f (w : W) : V := (M.connected w).nonempty.some.val
  have hf : ∀ w, f w ∈ M.branch w := fun w => (M.connected w).nonempty.some.property
  apply Fintype.card_le_of_injective f
  intro a b he
  by_contra hn
  exact Set.disjoint_left.mp (M.disjoint a b hn) (hf a) (he ▸ hf b)

noncomputable def model_singletons (G : SimpleGraph V) : MinorModel G G where
  branch v := {v}
  connected v := by
    have : Nonempty ({v} : Set V) := ⟨⟨v,rfl⟩⟩
    exact Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr hn
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,h⟩

noncomputable def model_relabel {W W' : Type} {G : SimpleGraph V}
    {H : SimpleGraph W} {H' : SimpleGraph W'} (M : MinorModel G H)
    (e : H ≃g H') : MinorModel G H' where
  branch w := M.branch (e.symm w)
  connected w := M.connected _
  disjoint u v hn := M.disjoint _ _ (fun h => hn (e.symm.injective h))
  adjacent := by intro u v h; exact M.adjacent (e.symm.map_rel_iff.mpr h)

lemma density_iso {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : density G = density H := by
  unfold density
  rw [e.card_edgeFinset_eq, e.card_eq]

theorem maximal_minor_density (G : SimpleGraph V) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      ∀ (W : Type) [Fintype W] [DecidableEq W] (J : SimpleGraph W),
        Nonempty (MinorModel G J) → density J ≤ density H := by
  classical
  let Family := Σ n : Fin (Fintype.card V + 1), SimpleGraph (Fin n.val)
  let candidates : Finset Family := Finset.univ.filter fun p => Nonempty (MinorModel G p.2)
  have hnon : candidates.Nonempty := by
    let p : Family := ⟨⟨Fintype.card V,by omega⟩,G.overFin rfl⟩
    refine ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact ⟨model_relabel (model_singletons G) (G.overFinIso rfl)⟩
  obtain ⟨p,hp,hmax⟩ := candidates.exists_max_image (fun p => density p.2) hnon
  refine ⟨p.1.val,p.2,(Finset.mem_filter.mp hp).2,?_⟩
  intro W _ _ J hJ
  obtain ⟨M⟩ := hJ
  let q : Family := ⟨⟨Fintype.card W,by have := model_card_le M; omega⟩,J.overFin rfl⟩
  have hq : q ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ⟨model_relabel M (J.overFinIso rfl)⟩⟩
  have hh := hmax q hq
  exact (density_iso (J.overFinIso rfl)).le.trans hh

def contractEdge (G : SimpleGraph V) (u v : V) : SimpleGraph {w : V // w ≠ v} where
  Adj a b := a ≠ b ∧ (G.Adj a.val b.val ∨
    (a.val = u ∧ G.Adj v b.val) ∨ (b.val = u ∧ G.Adj v a.val))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def contract_model (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    MinorModel G (contractEdge G u v) where
  branch w := if w.val = u then {u,v} else {w.val}
  connected w := by
    by_cases hw : w.val = u
    · rw [ite_eq_left hw]
      have he : {w | w ∈ (Walk.cons huv Walk.nil).support} = ({u,v} : Set V) := by
        ext w
        simp
      rw [← he]
      exact (Walk.cons huv Walk.nil).connected_induce_support
    · rw [ite_eq_right hw]
      have : Nonempty ({w.val} : Set V) := ⟨⟨w.val,rfl⟩⟩
      exact Connected.of_subsingleton
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    by_cases hau : a.val=u <;> by_cases hbu : b.val=u
    · exact hab (Subtype.ext (hau.trans hbu.symm))
    · simp only [ite_eq_left hau,ite_eq_right hbu,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl
      · exact hbu hb.symm
      · exact b.property hb.symm
    · simp only [ite_eq_right hau,ite_eq_left hbu,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      rcases hb with rfl | rfl
      · exact hau ha.symm
      · exact a.property ha.symm
    · simp only [ite_eq_right hau,ite_eq_right hbu,Set.mem_singleton_iff] at ha hb
      exact hab (Subtype.ext (ha.symm.trans hb))
  adjacent := by
    intro a b h
    have ha : a.val ∈ if a.val=u then ({u,v} : Set V) else {a.val} := by split_ifs with he <;> simp [*]
    have hb : b.val ∈ if b.val=u then ({u,v} : Set V) else {b.val} := by split_ifs with he <;> simp [*]
    rcases h.2 with h | h | h
    · exact ⟨_,ha,_,hb,h⟩
    · refine ⟨v,?_,b.val,hb,h.2⟩
      simp [h.1]
    · refine ⟨a.val,ha,v,?_,h.2.symm⟩
      simp [h.1]

noncomputable def common (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w

private def edgeGood (G : SimpleGraph V) (u v : V) (a b : V) : Prop :=
  G.Adj a b ∧ (a=v → b≠u ∧ ¬G.Adj u b) ∧ (b=v → a≠u ∧ ¬G.Adj u a)

private def proj (u v : V) (huv : u≠v) (w : V) : {z : V // z≠v} :=
  ⟨if w=v then u else w, by split_ifs with h; exact huv; exact h⟩

private lemma proj_collision {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b c d : V}
    (huv : u≠v) (ha : edgeGood G u v a b) (hc : edgeGood G u v c d)
    (hac : proj u v huv a = proj u v huv c)
    (hbd : proj u v huv b = proj u v huv d) : a=c := by
  have hcval := congrArg Subtype.val hac
  have hdval := congrArg Subtype.val hbd
  dsimp [proj] at hcval hdval
  by_cases hav : a=v
  · by_cases hcv : c=v
    · exact hav.trans hcv.symm
    · have hcu : c=u := by simpa [hav,hcv] using hcval.symm
      have hp := ha.2.1 hav
      have hb : b≠v := by intro he; exact ha.1.ne (hav.trans he.symm)
      have hd : d≠v := by
        intro he
        exact hp.1 (by simpa [he,hb] using hdval)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hcu ▸ hbe.symm ▸ hc.1)).elim
  · by_cases hcv : c=v
    · have hau : a=u := by simpa [hav,hcv] using hcval
      have hp := hc.2.1 hcv
      have hd : d≠v := by intro he; exact hc.1.ne (hcv.trans he.symm)
      have hb : b≠v := by
        intro he
        exact hp.1 (by simpa [he,hd] using hdval.symm)
      have hbe : b=d := by simpa [hb,hd] using hdval
      exact (hp.2 (hau ▸ hbe ▸ ha.1)).elim
    · simpa [hav,hcv] using hcval

private lemma proj_adj {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {u v a b : V} (huv : u≠v)
    (ha : edgeGood G u v a b) :
    (contractEdge G u v).Adj (proj u v huv a) (proj u v huv b) := by
  refine ⟨?_,?_⟩
  · intro he
    have hv := congrArg Subtype.val he
    dsimp [proj] at hv
    by_cases hav : a=v <;> by_cases hbv : b=v
    · exact ha.1.ne (hav.trans hbv.symm)
    · exact (ha.2.1 hav).1 (by simpa [hav,hbv] using hv.symm)
    · exact (ha.2.2 hbv).1 (by simpa [hav,hbv] using hv)
    · exact ha.1.ne (by simpa [hav,hbv] using hv)
  · by_cases hav : a=v <;> by_cases hbv : b=v
    · exact (ha.1.ne (hav.trans hbv.symm)).elim
    · right; left
      exact ⟨by simp [proj,hav], by simpa [proj,hbv,hav] using ha.1⟩
    · right; right
      exact ⟨by simp [proj,hbv], by simpa [proj,hbv,hav] using ha.1.symm⟩
    · left
      simpa [proj,hav,hbv] using ha.1

theorem contract_edge_count (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    G.edgeFinset.card ≤ (contractEdge G u v).edgeFinset.card + 1 + (common G u v).card := by
  classical
  let D := Density.darts G Finset.univ
  let good := D.filter fun z => edgeGood G u v z.1 z.2
  let bad := D \ good
  let N := insert u (common G u v)
  have hN : N.card ≤ 1+(common G u v).card := by
    exact (Finset.card_insert_le _ _).trans (by omega)
  have hbad : bad ⊆ N.image (fun w => (v,w)) ∪ N.image (fun w => (w,v)) := by
    intro z hz
    have hzD := (Finset.mem_sdiff.mp hz).1
    have hzG : G.Adj z.1 z.2 := (Finset.mem_filter.mp hzD).2
    have hng : ¬edgeGood G u v z.1 z.2 := by
      intro hg
      exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_filter.mpr ⟨hzD,hg⟩)
    by_cases hfst : z.1=v
    · by_cases hleft : z.2≠u ∧ ¬G.Adj u z.2
      · have hright : z.2=v → z.1≠u ∧ ¬G.Adj u z.1 := by
          intro he; exact (hzG.ne (hfst.trans he.symm)).elim
        exact (hng ⟨hzG,fun _ => hleft,hright⟩).elim
      · have hmem : z.2 ∈ N := by
          dsimp [N]
          by_cases hzu : z.2=u
          · exact Finset.mem_insert.mpr (Or.inl hzu)
          · have had : G.Adj u z.2 := by tauto
            exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _,had,hfst ▸ hzG⟩))
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.2,hmem,Prod.ext hfst.symm rfl⟩)
    · have hsnd : z.2=v := by
        by_contra hn
        exact hng ⟨hzG,fun he => (hfst he).elim,fun he => (hn he).elim⟩
      have hright : ¬(z.1≠u ∧ ¬G.Adj u z.1) := by
        intro hr; exact hng ⟨hzG,fun he => (hfst he).elim,fun _ => hr⟩
      have hmem : z.1 ∈ N := by
        dsimp [N]
        by_cases hzu : z.1=u
        · exact Finset.mem_insert.mpr (Or.inl hzu)
        · have had : G.Adj u z.1 := by tauto
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,had,hsnd ▸ hzG.symm⟩))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z.1,hmem,Prod.ext rfl hsnd.symm⟩)
  have hbadcard : bad.card ≤ 2*(1+(common G u v).card) := by
    have hb := (Finset.card_le_card hbad).trans (Finset.card_union_le _ _)
    have h₁ := Finset.card_image_le (s := N) (f := fun w => (v,w))
    have h₂ := Finset.card_image_le (s := N) (f := fun w => (w,v))
    omega
  let f (z : V×V) := (proj u v huv.ne z.1,proj u v huv.ne z.2)
  have hf : Set.InjOn f (↑good : Set (V×V)) := by
    intro a ha b hb he
    have hag := (Finset.mem_filter.mp ha).2
    have hbg := (Finset.mem_filter.mp hb).2
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    refine Prod.ext (proj_collision huv.ne hag hbg hfst hsnd) ?_
    exact proj_collision huv.ne ⟨hag.1.symm,hag.2.2,hag.2.1⟩
      ⟨hbg.1.symm,hbg.2.2,hbg.2.1⟩ hsnd hfst
  have hfD : good.image f ⊆ Density.darts (contractEdge G u v) Finset.univ := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨by simp,proj_adj huv.ne (Finset.mem_filter.mp ha).2⟩
  have hgcard : good.card ≤ (Density.darts (contractEdge G u v) Finset.univ).card := by
    rw [← Finset.card_image_of_injOn hf]
    exact Finset.card_le_card hfD
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun z => edgeGood G u v z.1 z.2) D)
  change bad.card + good.card = D.card at hsum
  have hD : D.card = 2*G.edgeFinset.card := Density.darts_univ G
  rw [Density.darts_univ] at hgcard
  omega

lemma density_mul_order {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    density G * Fintype.card V = (G.edgeFinset.card : ℚ) := by
  unfold density
  exact div_mul_cancel₀ _ (by exact_mod_cast hn.ne')

lemma density_nonneg {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : 0 ≤ density G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma degree_le_twice_density (G : SimpleGraph V) (hn : 0 < Fintype.card V) :
    ∃ u, (G.degree u : ℚ) ≤ 2*density G := by
  classical
  by_contra! h
  have hab := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (f := fun _ : V => 2*density G) (g := fun v => (G.degree v : ℚ))
    (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)) (fun v _ => h v)
  have hsum : (∑ v, (G.degree v : ℚ)) = 2*(G.edgeFinset.card : ℚ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hab
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hab
  have he := density_mul_order G hn
  nlinarith

lemma common_of_max_density (G : SimpleGraph V) (hmax : ∀ (W : Type) [Fintype W]
    [DecidableEq W] (J : SimpleGraph W), Nonempty (MinorModel G J) → density J ≤ density G)
    {u v : V} (huv : G.Adj u v) : density G ≤ 1+(common G u v).card := by
  classical
  let H := contractEdge G u v
  have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u,v,huv.ne⟩
  have hn' : Fintype.card {w : V // w ≠ v} = Fintype.card V - 1 := by
    simp
  have hh : 0 < Fintype.card {w : V // w≠v} := by omega
  have heH := density_mul_order H hh
  have heG := density_mul_order G (by omega)
  have hcount : (G.edgeFinset.card : ℚ) ≤ (H.edgeFinset.card : ℚ)+1+(common G u v).card :=
    by exact_mod_cast contract_edge_count G huv
  have hle := hmax _ H ⟨contract_model G huv⟩
  have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℚ) ≤ Fintype.card {w : V // w≠v} by positivity)
  rw [heH,hn',Nat.cast_sub (by omega : 1 ≤ Fintype.card V)] at hmul
  norm_num only [Nat.cast_one] at hmul
  nlinarith

noncomputable def model_induce (G : SimpleGraph V) (S : Finset V) :
    MinorModel G (G.induce (↑S : Set V)) where
  branch w := {w.val}
  connected w := by
    have : Nonempty ({w.val} : Set V) := ⟨⟨w.val,rfl⟩⟩
    exact Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr (fun he => hn (Subtype.ext he))
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,h⟩

lemma neighborhood_degree (G : SimpleGraph V) (u : V) (v : ↥(G.neighborFinset u)) :
    ((G.induce (↑(G.neighborFinset u) : Set V)).degree v) = (common G u v.val).card := by
  classical
  have he : ((G.induce (↑(G.neighborFinset u) : Set V)).neighborFinset v).image Subtype.val =
      common G u v.val := by
    ext w
    simp only [Finset.mem_image,SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj,
      common,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).mp z.property,hz⟩
    · rintro ⟨hw,hv⟩
      exact ⟨⟨w,(SimpleGraph.mem_neighborFinset _ _ _).mpr hw⟩,hv,rfl⟩
  rw [← he,Finset.card_image_of_injective _ Subtype.val_injective,
    SimpleGraph.card_neighborFinset_eq_degree]

lemma kConnected_iso {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) : KConnectedOn H Finset.univ k := by
  classical
  refine ⟨?_,?_⟩
  · simpa only [Finset.card_univ,← e.card_eq] using hc.1
  · intro X _ hX
    let Z := X.image e.symm
    have hZ : Z.card < k := by simpa [Z,Finset.card_image_of_injective _ e.symm.injective] using hX
    have hconn := hc.2 Z (Finset.subset_univ _) hZ
    let f : (G.induce (↑(Finset.univ \ Z) : Set V)) →g
        (H.induce (↑(Finset.univ \ X) : Set W)) :=
      { toFun := fun v => ⟨e v.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv =>
          (Finset.mem_sdiff.mp v.property).2
            (Finset.mem_image.mpr ⟨e v.val,hv,e.symm_apply_apply v.val⟩)⟩⟩
        map_rel' := by intro u v h; exact e.map_rel_iff.mpr h }
    apply hconn.map f
    intro w
    have hw : e.symm w.val ∈ Finset.univ \ Z := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      intro hz
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_sdiff.mp w.property).2 (e.symm.injective he ▸ ha)
    exact ⟨⟨e.symm w.val,hw⟩,Subtype.ext (e.apply_symm_apply w.val)⟩

theorem small_minor_core (G : SimpleGraph V) (hlower : (16 : ℚ) ≤ density G) :
    ∃ (n k : ℕ) (H : SimpleGraph (Fin n)), Nonempty (MinorModel G H) ∧
      KConnectedOn H Finset.univ k ∧ n ≤ 32*k ∧
      density G < 8*(k+1) := by
  classical
  obtain ⟨q,J,⟨M⟩,hmax⟩ := maximal_minor_density G
  have hdiag := hmax V G ⟨model_singletons G⟩
  have hd : (16 : ℚ) ≤ density J := hlower.trans hdiag
  have hJmax : ∀ (W : Type) [Fintype W] [DecidableEq W] (L : SimpleGraph W),
      Nonempty (MinorModel J L) → density L ≤ density J := by
    intro W _ _ L hL
    obtain ⟨N⟩ := hL
    exact hmax W L ⟨compose_model M N⟩
  have hJ : 0 < Fintype.card (Fin q) := by
    by_contra hn
    have hh : Fintype.card (Fin q)=0 := by omega
    norm_num [density,hh] at hd
  let k := ⌊density J / 8⌋₊
  have hk : 2 ≤ k := Nat.le_floor (by linarith : (2 : ℚ) ≤ density J/8)
  have hklo : (8*k : ℚ) ≤ density J := by
    have hh := Nat.floor_le (by linarith : (0 : ℚ) ≤ density J/8)
    change (k : ℚ) ≤ density J/8 at hh
    linarith
  have hkhi : density J < 8*((k : ℚ)+1) := by
    have hh := Nat.lt_floor_add_one (density J/8)
    change density J/8 < (k : ℚ)+1 at hh
    linarith
  obtain ⟨u,hu⟩ := degree_le_twice_density J hJ
  let S := J.neighborFinset u
  let : Fintype (↑S : Set (Fin q)) := inferInstanceAs (Fintype ↥S)
  let L := J.induce (↑S : Set (Fin q))
  have hS : (S.card : ℚ) ≤ 2*density J := by simpa [S] using hu
  have hdeg : ∀ v : ↥S, (8*k : ℚ)-1 ≤ L.degree v := by
    intro v
    have hv := common_of_max_density J hJmax ((SimpleGraph.mem_neighborFinset _ _ _).mp v.property)
    rw [← neighborhood_degree J u v] at hv
    linarith
  have hSpos : 0 < S.card := by
    by_contra hn
    have he : S.card=0 := by omega
    have hdu : J.degree u=0 := by simpa [S] using he

    let T : Finset (Fin q) := Finset.univ.erase u
    let : Fintype (↑T : Set (Fin q)) := inferInstanceAs (Fintype ↥T)
    let P := J.induce (↑T : Set (Fin q))
    have hT : T.card+1=q := by
      have := Finset.card_erase_add_one (Finset.mem_univ u)
      simpa [T] using this
    have hed : P.edgeFinset.card = J.edgeFinset.card := by
      have hs : (↑T : Set (Fin q)) = {u}ᶜ := by ext w; simp [T]
      dsimp [P]
      have hh := SimpleGraph.card_edgeFinset_induce_compl_singleton J u
      rw [SimpleGraph.card_edgeFinset_deleteIncidenceSet,hdu,Nat.sub_zero] at hh
      let e : P ≃g (J.induce {u}ᶜ) :=
        { toEquiv := Set.equivOfEq hs
          map_rel_iff' := by intro a b; rfl }
      exact e.card_edgeFinset_eq.trans hh
    have hql : 1 < q := by
      by_contra hn
      have hqpos : 0<q := by simpa using hJ
      have hq : q=1 := by omega
      have hc : J.edgeFinset.card=0 := by
        have hh := SimpleGraph.card_edgeFinset_le_card_choose_two (G := J)
        simp only [Fintype.card_fin,hq] at hh
        norm_num at hh
        simp [hh]
      norm_num [density,hc] at hd
    have htpos : 0 < Fintype.card ↥T := by simpa using (show 0<T.card by omega)
    have hPmax := hJmax _ P ⟨model_induce J T⟩
    have heP := density_mul_order P htpos
    have heJ := density_mul_order J hJ
    erw [hed] at heP
    have htc : (Fintype.card ↥T : ℚ)+1 = Fintype.card (Fin q) := by
      exact_mod_cast (by simpa using hT : Fintype.card ↥T+1=Fintype.card (Fin q))
    have hm := mul_le_mul_of_nonneg_right hPmax (show (0 : ℚ) ≤ Fintype.card ↥T by positivity)
    have heP' : density P * (T.card : ℚ) = (J.edgeFinset.card : ℚ) := by
      have hh : Fintype.card (↑T : Set (Fin q)) = T.card := Fintype.card_coe T
      erw [hh] at heP
      exact heP
    have hm' : density P * (T.card : ℚ) ≤ density J * (T.card : ℚ) := by
      simpa only [Fintype.card_coe] using hm
    have htc' : (T.card : ℚ)+1 = Fintype.card (Fin q) := by simpa only [Fintype.card_coe] using htc
    nlinarith [heP',hm',htc']
  have hedge : 2*k*Fintype.card ↥S < L.edgeFinset.card := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hdeg v)
    have hsum : (∑ v, (L.degree v : ℚ)) = 2*(L.edgeFinset.card : ℚ) := by
      exact_mod_cast L.sum_degrees_eq_twice_card_edges
    erw [hsum] at hs
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
    have hn : (0 : ℚ) < Fintype.card ↥S := by exact_mod_cast (by simpa using hSpos : 0<Fintype.card ↥S)
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (2*k*Fintype.card ↥S : ℚ)<L.edgeFinset.card := by nlinarith
    exact_mod_cast hh
  obtain ⟨T,hTc⟩ := Density.edge_density_connectivity L (by omega) hedge
  let : Fintype (↑T : Set ↥S) := inferInstanceAs (Fintype ↥T)
  let H := L.induce (↑T : Set ↥S)
  have hHc := induce_connected L T hTc
  let N := compose_model M (compose_model (model_induce J S) (model_induce L T))
  let e := H.overFinIso rfl
  refine ⟨Fintype.card ↥T,k,H.overFin rfl,⟨model_relabel N e⟩,?_,?_,?_⟩
  ·
    exact kConnected_iso e hHc
  · have ht : T.card ≤ S.card := by simpa using Finset.card_le_univ T
    have hkq : (2 : ℚ) ≤ k := by exact_mod_cast hk
    have hh : (S.card : ℚ) ≤ 32*k := by nlinarith
    exact (by simpa using ht : Fintype.card ↥T ≤ S.card).trans (by exact_mod_cast hh)
  · exact hdiag.trans_lt hkhi

lemma kConnected_mono {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S : Finset V} {k l : ℕ}
    (hc : KConnectedOn G S k) (hl : l≤k) : KConnectedOn G S l :=
  ⟨hl.trans_lt hc.1,fun X hX hx => hc.2 X hX (hx.trans_le hl)⟩

lemma kConnected_restrict {G : SimpleGraph V} {k z : ℕ}
    (hc : KConnectedOn G Finset.univ k) (T : Finset V)
    (hloss : Fintype.card V ≤ T.card+z) (hz : z<k) : KConnectedOn G T (k-z) := by
  classical
  let X := Finset.univ \ T
  have hsum : X.card+T.card=Fintype.card V := by
    simpa [X] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hX : X.card<k := by omega
  have hc' := delete_connected G hc (Finset.subset_univ X) hX
  have he : Finset.univ \ X=T := by ext v; simp [X]
  rw [he] at hc'
  exact kConnected_mono hc' (by omega)

lemma density_of_connectivity (G : SimpleGraph V) {k : ℕ}
    (hc : KConnectedOn G Finset.univ k) : (k : ℚ) ≤ 2*density G := by
  classical
  have hn : 0<Fintype.card V := by have := hc.1; simpa only [Finset.card_univ] using (Nat.zero_le k).trans_lt this
  have hd : ∀ v, k ≤ G.degree v := by
    intro v
    have hh := min_degree G hc (Finset.mem_univ v)
    have he : Density.neighbors G Finset.univ v=G.neighborFinset v := by ext w; simp [Density.neighbors]
    rwa [he,SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hd v)
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hs
  have hsq : (Fintype.card V : ℚ)*k ≤ 2*G.edgeFinset.card := by exact_mod_cast hs
  have he := density_mul_order G hn
  have hnq : (0 : ℚ)<Fintype.card V := by exact_mod_cast hn
  nlinarith

lemma bags_meeting_bound {V : Type} [Fintype V] [DecidableEq V] {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : MinorModel G H) (A : Finset V) :
    (Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j).card ≤ A.card := by
  classical
  let X := Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j
  have hx : ∀ j : ↥X, ∃ a : ↥A, a.val ∈ M.branch j.val := by
    intro j
    obtain ⟨a,ha,hab⟩ := (Finset.mem_filter.mp j.property).2
    exact ⟨⟨a,ha⟩,hab⟩
  choose f hf using hx
  have hinj : Function.Injective f := by
    intro j l he
    by_contra hn
    exact Set.disjoint_left.mp (M.disjoint j.val l.val (fun h => hn (Subtype.ext h)))
      (hf j) (he ▸ hf l)
  have hh := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe,Fintype.card_coe] at hh
  exact hh

theorem group_terminals {I : Type} [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (A : Finset V) (label : ↥A → I)
    (hsurj : Function.Surjective label) (hA : 1≤A.card)
    (hc : KConnectedOn G Finset.univ (65536*A.card)) :
    ∃ B : I → Set V,
      (∀ i, (G.induce (B i)).Connected) ∧
      (∀ i j, i≠j → Disjoint (B i) (B j)) ∧
      (∀ a : ↥A, a.val ∈ B (label a)) := by
  classical
  have hd := density_of_connectivity G hc
  have hm : (1 : ℚ)≤A.card := by exact_mod_cast hA
  have hdlow : (32768 : ℚ)*A.card ≤ density G := by push_cast at hd; linarith
  obtain ⟨n,k,H,⟨M⟩,hH,hsize,hdbound⟩ := small_minor_core G (by linarith)
  have hk : 4096*A.card ≤ k := by
    have hh : (4096*A.card : ℚ)<k+1 := by linarith
    have hh' : 4096*A.card<k+1 := by exact_mod_cast hh
    omega
  let X : Finset (Fin n) := Finset.univ.filter fun j => ∃ a∈A, a∈M.branch j
  have hX : X.card≤A.card := bags_meeting_bound M A
  let S : Finset (Fin n) := Finset.univ \ X
  have hSc : KConnectedOn H S (k-X.card) := delete_connected H hH (Finset.subset_univ X) (by omega)
  let L := H.induce (↑S : Set (Fin n))
  have hLc : KConnectedOn L Finset.univ (k-X.card) := induce_connected H S hSc
  let N := compose_model M (model_induce H S)
  have hbranch : ∀ j : ↥S, N.branch j = M.branch j.val := by
    intro j
    ext v
    simp only [N,compose_model,MinorModel.expand,model_induce,Set.mem_ofPred_eq,Set.mem_singleton_iff]
    constructor
    · rintro ⟨w,hw,hv⟩
      simpa only [hw] using hv
    · exact fun hv => ⟨j.val,rfl,hv⟩
  have haB : ∀ j, Disjoint (↑A : Set V) (N.branch j) := by
    intro j
    apply Set.disjoint_left.mpr
    intro a ha hab
    exact (Finset.mem_sdiff.mp j.property).2
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,ha,(hbranch j) ▸ hab⟩)
  have hendegree : ∀ j, 3*A.card≤(Density.neighbors L Finset.univ j).card := by
    intro j
    exact (by omega : 3*A.card≤k-X.card).trans (min_degree L hLc (Finset.mem_univ j))
  have hlorder : 3*A.card ≤ Fintype.card ↥S := by
    have ho := hLc.1
    simp only [Finset.card_univ] at ho
    have he : Fintype.card (↑S : Set (Fin n))=S.card := Fintype.card_coe S
    erw [he] at ho
    rw [Fintype.card_coe]
    omega
  obtain ⟨T,hTcard,P,f,hf,hroot⟩ := root_minor_core G L A N
    (kConnected_mono hc (by omega)) haB hendegree hlorder
  have hloss : k-X.card-(2*A.card) ≥ k-3*A.card := by omega
  have hTc : KConnectedOn L T (k-3*A.card) := kConnected_mono
    (kConnected_restrict hLc T hTcard (by omega)) hloss
  let Q := L.induce (↑T : Set ↥S)
  have hQc : KConnectedOn Q Finset.univ (k-3*A.card) := induce_connected L T hTc
  have hQorder : Fintype.card ↥T ≤ 64*(k-3*A.card) := by
    have ht : T.card≤Fintype.card ↥S := Finset.card_le_univ T
    have hs : S.card≤n := by simpa using Finset.card_le_univ S
    have hts : T.card≤n := (by simpa using ht : T.card≤S.card).trans hs
    have hnum : n≤64*(k-3*A.card) := by omega
    simpa using hts.trans hnum
  let A' : Finset ↥T := Finset.univ.image f
  have hAcard : A'.card=A.card := by simp [A',Finset.card_image_of_injective _ hf]
  let ff : ↥A → ↥A' := fun a => ⟨f a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩
  have hff : Function.Bijective ff := by
    constructor
    · intro a b he
      exact hf (congrArg Subtype.val he)
    · intro b
      obtain ⟨a,_,ha⟩ := Finset.mem_image.mp b.property
      exact ⟨a,Subtype.ext ha⟩
  let e := Equiv.ofBijective ff hff
  let label' : ↥A' → I := fun b => label (e.symm b)
  have hsurj' : Function.Surjective label' := hsurj.comp e.symm.surjective
  obtain ⟨B,hBc,hBd,hBroot⟩ := group_small_core Q A' label' hsurj'
    (by simpa only [hAcard] using hA) 64 (k-3*A.card) hQc hQorder (by rw [hAcard]; omega)
  refine ⟨fun i => P.expand (↑(B i) : Set ↥T),?_,?_,?_⟩
  · intro i
    exact P.expand_connected (hBc i)
  · intro i j hij
    exact P.expand_disjoint (by exact_mod_cast hBd i j hij)
  · intro a
    refine ⟨f a,?_,hroot a⟩
    have hh := hBroot (e a)
    change f a ∈ B (label (e.symm (e a))) at hh
    rw [e.symm_apply_apply] at hh
    exact hh

end LinearListHadwiger.Knitting

end OAI
