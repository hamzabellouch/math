import OAI.Combinatorics.ListHadwiger.MinorModels

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagContraction
variable {V J : Type} (G : SimpleGraph V) (B : J → Set V)

def Remnant : Set V := {v | ∀ j, v ∉ B j}
abbrev Vertex := ↥(Remnant B) ⊕ J

def branch : Vertex B → Set V
  | .inl v => {v.val}
  | .inr j => B j

def graph : SimpleGraph (Vertex B) where
  Adj u v := u ≠ v ∧ ∃ x ∈ branch B u, ∃ y ∈ branch B v, G.Adj x y
  symm := ⟨by
    rintro u v ⟨huv, x, hx, y, hy, hxy⟩
    exact ⟨huv.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance [Fintype V] [Fintype J] : Fintype (Vertex B) := by
  classical
  exact Fintype.ofFinite _

lemma branch_disjoint (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (u v : Vertex B) (huv : u ≠ v) : Disjoint (branch B u) (branch B v) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases u with
  | inl u =>
    have hxu : x = u.val := hx
    cases v with
    | inl v => exact huv (congrArg Sum.inl (Subtype.ext (hxu.symm.trans hy)))
    | inr j => exact u.property j (hxu ▸ hy)
  | inr i =>
    cases v with
    | inl v => exact v.property i ((show x = v.val from hy) ▸ hx)
    | inr j => exact Set.disjoint_left.mp (hd i j (fun h => huv (h ▸ rfl))) hx hy

def model (hc : ∀ j, (G.induce (B j)).Connected)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j)) : MinorModel G (graph G B) where
  branch := branch B
  connected := by
    intro w
    cases w with
    | inl v =>
      change (G.induce {v.val}).Connected
      exact SimpleGraph.Connected.of_subsingleton
    | inr j => exact hc j
  disjoint := branch_disjoint B hd
  adjacent := by intro u v h; exact h.2

def liftSet (C : Set V) : Set (Vertex B) :=
  {w | match w with | .inl v => v.val ∈ C | .inr _ => False}

lemma liftSet_connected {C : Set V} (hC : C ⊆ Remnant B)
    (hc : (G.induce C).Connected) : ((graph G B).induce (liftSet B C)).Connected := by
  let f : G.induce C →g (graph G B).induce (liftSet B C) :=
    { toFun := fun v => ⟨Sum.inl ⟨v.val, hC v.property⟩, v.property⟩
      map_rel' := by
        intro u v huv
        refine ⟨?_, u.val, rfl, v.val, rfl, huv⟩
        intro heq
        apply huv.ne
        apply Subtype.ext
        exact congrArg (fun w : Vertex B => match w with
          | .inl z => z.val
          | .inr _ => u.val) heq }
  apply hc.map f
  intro w
  rcases w with ⟨w, hw⟩
  cases w with
  | inl v => exact ⟨⟨v.val, hw⟩, rfl⟩
  | inr j => exact hw.elim

lemma liftSet_disjoint {C D : Set V} (hCD : Disjoint C D) :
    Disjoint (liftSet B C) (liftSet B D) := by
  apply Set.disjoint_left.mpr
  intro w hw hw'
  cases w with
  | inl v => exact Set.disjoint_left.mp hCD hw hw'
  | inr j => exact hw.elim

lemma liftSet_adj_target {C : Set V} (hC : C ⊆ Remnant B) {j : J}
    (h : ∃ x ∈ C, ∃ y ∈ B j, G.Adj x y) :
    ∃ w ∈ liftSet B C, (graph G B).Adj w (.inr j) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact ⟨.inl ⟨x, hC hx⟩, hx, Sum.inl_ne_inr, x, rfl, y, hy, hxy⟩

end BagContraction

namespace BagRouting
variable {V J : Type} {G : SimpleGraph V} {A : Finset V} {B : J → Set V}

def region (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (i : ↥A × Bool) : Set V :=
  {v | v ∈ (D.paths i).2.val.support} ∪ B (D.bag i)

lemma region_connected (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hc : ∀ j, (G.induce (B j)).Connected) (i : ↥A × Bool) :
    (G.induce (D.region i)).Connected := by
  exact SimpleGraph.induce_union_connected
    (D.paths i).2.val.connected_induce_support.preconnected (hc (D.bag i)).preconnected
    ⟨(D.paths i).1, (D.paths i).2.val.end_mem_support, D.endpoint_mem i⟩

lemma root_mem_region (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (i : ↥A × Bool) : i.1.val ∈ D.region i :=
  Or.inl (D.paths i).2.val.start_mem_support

lemma region_congestion (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hA : ∀ j, Disjoint (↑A : Set V) (B j)) (v : V) :
    (Finset.univ.filter fun i => v ∈ D.region i).card ≤ 2 := by
  classical
  let R : Finset (↥A × Bool) := Finset.univ.filter fun i => v ∈ (D.paths i).2.val.support
  let T : Finset (↥A × Bool) := Finset.univ.filter fun i => v ∈ B (D.bag i)
  have hRT : (Finset.univ.filter fun i => v ∈ D.region i) = R ∪ T := by
    ext i
    simp [R, T, region]
  have hR : R.card ≤ 2 := by
    have hle : R.card ≤ (Finset.univ : Finset Bool).card :=
      Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _) (by
        intro i hi j hj hij
        by_cases heq : i = j
        · exact heq
        have hh := D.overlap i j heq v (Finset.mem_filter.mp hi).2
          (Finset.mem_filter.mp hj).2
        exact Prod.ext (Subtype.ext (hh.1.symm.trans hh.2)) hij)
    simpa using hle
  by_cases hvA : v ∈ A
  · have hT : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact Set.disjoint_left.mp (hA (D.bag i)) hvA (Finset.mem_filter.mp hi).2
    simpa [hRT, hT] using hR
  · have hR1 : R.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hh := D.overlap i j hij v (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
      exact hvA (hh.1 ▸ i.1.property)
    have hT1 : T.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hne : D.bag i ≠ D.bag j := fun hh => hij (D.bag_injective hh)
      exact Set.disjoint_left.mp (hd _ _ hne) (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    rw [hRT]
    exact (Finset.card_union_le R T).trans (by omega)

lemma region_avoids_unused (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (havoid : ∀ j, j ∉ Set.range D.bag → ∀ i v,
      v ∈ (D.paths i).2.val.support → v ∉ B j)
    (j : J) (hj : j ∉ Set.range D.bag) (i : ↥A × Bool) :
    Disjoint (D.region i) (B j) := by
  apply Set.disjoint_left.mpr
  intro v hv hvj
  rcases hv with hvp | hvb
  · exact havoid j hj i v hvp hvj
  · have hne : D.bag i ≠ j := fun hh => hj ⟨i, hh⟩
    exact Set.disjoint_left.mp (hd _ _ hne) hvb hvj

end BagRouting

theorem packing_from_regions {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    (C : I → Set V) (s : I → V) (c : ℕ) (hc : 0 < c)
    (hs : ∀ i, s i ∈ A) (hsC : ∀ i, s i ∈ C i)
    (hC : ∀ i, (G.induce (C i)).Connected)
    (hadj : ∀ i b, b ∈ B → ∃ w ∈ C i, G.Adj w b)
    (hcon : ∀ v, (Finset.univ.filter fun i => v ∈ C i).card ≤ c)
    (hI : c * A.card ≤ Fintype.card I) (hB : A.card ≤ B.card) :
    Nonempty (FullPacking G A B) := by
  classical
  apply fullPacking_of_no_small_separator
  intro X hX
  obtain ⟨i, hi⟩ := exists_region_avoiding C X c A.card hc hI hX (fun v _ => hcon v)
  have hn : ¬B ⊆ X := fun h => (Nat.not_le_of_lt (hX.trans_le hB)) (Finset.card_le_card h)
  simp only [Finset.subset_iff, not_forall] at hn
  obtain ⟨b, hb, hbX⟩ := hn
  obtain ⟨w, hw, hwb⟩ := hadj i b hb
  obtain ⟨p⟩ := (hC i).preconnected ⟨s i, hsC i⟩ ⟨w, hw⟩
  let q : G.Walk (s i) w := p.map (Embedding.induce (C i)).toHom
  refine ⟨s i, hs i, b, hb, q.append hwb.toWalk, ?_⟩
  intro v hv
  rw [Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · have hv' : v ∈ (p.map (Embedding.induce (C i)).toHom).support := hv
    rw [Walk.support_map] at hv'
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hv'
    exact hi z.val z.property
  · have hv' : v = w ∨ v = b := by simpa using hv
    rcases hv' with rfl | rfl
    · exact hi _ hw
    · exact hbX

def RootedCliqueModel.reindex {V I J : Type} {G : SimpleGraph V} {r : I → V}
    (M : RootedCliqueModel G r) (f : J → I) (hf : Function.Injective f) :
    RootedCliqueModel G (r ∘ f) where
  branch j := M.branch (f j)
  connected j := M.connected (f j)
  disjoint i j h := M.disjoint (f i) (f j) (fun hh => h (hf hh))
  adjacent i j h := M.adjacent (f i) (f j) (fun hh => h (hf hh))
  root_mem j := M.root_mem (f j)

theorem rooting_from_eligible {V J : Type} [Fintype V] [Fintype J]
    [DecidableEq V] (G : SimpleGraph V) (A : Finset V) (B : J → Set V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hcB : ∀ j, (G.induce (B j)).Connected)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (haB : ∀ j, Disjoint (↑A : Set V) (B j))
    (heB : ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y)
    (hcard : 3 * A.card ≤ Fintype.card J) :
    Nonempty (RootedCliqueModel G (fun a : ↥A => a.val)) := by
  classical
  obtain ⟨D, hD⟩ := BagRouting.exists_avoiding_unused hdB
    (bagRouting_of_double_packing G A B hc hcB hdB haB (by omega))
  let T : Finset J := Finset.univ \ Finset.univ.image D.bag
  have hT : A.card ≤ T.card := by
    have hi : (Finset.univ.image D.bag).card = 2 * A.card := by
      simp [Finset.card_image_of_injective _ D.bag_injective, Nat.mul_comm]
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Finset.univ.image D.bag))
    simp only [Finset.card_univ] at hh
    dsimp [T]
    omega
  have hunused : ∀ j : ↥T, j.val ∉ Set.range D.bag := by
    intro j ⟨i, hi⟩
    exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  let BT : ↥T → Set V := fun j => B j.val
  let W := BagContraction.Vertex BT
  let H := BagContraction.graph G BT
  have hreg : ∀ i : ↥A × Bool, D.region i ⊆ BagContraction.Remnant BT := by
    intro i v hv j hvj
    exact Set.disjoint_left.mp (D.region_avoids_unused hdB hD j.val (hunused j) i) hv hvj
  have harem : ∀ a : ↥A, a.val ∈ BagContraction.Remnant BT := by
    intro a j hj
    exact Set.disjoint_left.mp (haB j.val) a.property hj
  let src : ↥A → W := fun a => .inl ⟨a.val, harem a⟩
  have hsrc : Function.Injective src := by
    intro a b hab
    have hh : (⟨a.val, harem a⟩ : ↥(BagContraction.Remnant BT)) = ⟨b.val, harem b⟩ := Sum.inl.inj hab
    apply Subtype.ext
    exact congrArg (fun z : ↥(BagContraction.Remnant BT) => z.val) hh
  let AS : Finset W := Finset.univ.image src
  let TS : Finset W := Finset.univ.image (Sum.inr : ↥T → W)
  have hAS : AS.card = A.card := by simp [AS, Finset.card_image_of_injective _ hsrc]
  have hTS : TS.card = T.card := by
    simp [TS, Finset.card_image_of_injective _ Sum.inr_injective]
  let C := fun i : ↥A × Bool => BagContraction.liftSet BT (D.region i)
  have hcon : ∀ w : W, (Finset.univ.filter fun i => w ∈ C i).card ≤ 2 := by
    intro w
    cases w with
    | inl v => exact D.region_congestion hdB haB v.val
    | inr j =>
      have he : (Finset.univ.filter fun i => (Sum.inr j : W) ∈ C i) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hh : False := (Finset.mem_filter.mp hi).2
        exact hh
      rw [he]
      simp
  have hadj : ∀ i b, b ∈ TS → ∃ w ∈ C i, H.Adj w b := by
    intro i b hb
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    apply BagContraction.liftSet_adj_target G BT (hreg i)
    have hne : D.bag i ≠ j.val := fun hh => hunused j ⟨i, hh⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := heB _ _ hne
    exact ⟨x, Or.inr hx, y, hy, hxy⟩
  obtain ⟨P⟩ := packing_from_regions H AS TS C (fun i => src i.1) 2 (by omega)
    (fun i => Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, rfl⟩)
    (fun i => D.root_mem_region i)
    (fun i => BagContraction.liftSet_connected G BT (hreg i) (D.region_connected hcB i))
    hadj hcon (by simp [hAS, Fintype.card_prod, Nat.mul_comm]) (by omega)
  let M := BagContraction.model G BT (fun j => hcB j.val)
    (fun i j hij => hdB i.val j.val (fun h => hij (Subtype.ext h)))
  have hcl : ∀ x ∈ TS, ∀ y ∈ TS, x ≠ y → H.Adj x y := by
    intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨hxy, ?_⟩
    exact heB i.val j.val (fun h => hxy (congrArg Sum.inr (Subtype.ext h)))
  have hroot : ∀ a : ↥AS, ∃ v : V, v ∈ M.branch a.val := by
    intro a
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp a.property
    exact ⟨i.val, by rw [← hi]; exact rfl⟩
  choose r hr using hroot
  obtain ⟨N⟩ := rootedModel_of_packing M P hcl r hr
  let f : ↥A → ↥AS := fun a => ⟨src a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Injective f := fun _ _ h => hsrc (congrArg Subtype.val h)
  have heq : r ∘ f = fun a : ↥A => a.val := by
    funext a
    exact hr (f a)
  rw [← heq]
  exact ⟨N.reindex f hf⟩

lemma eligible_bags_card {V J : Type} [Fintype J] [DecidableEq V]
    (A : Finset V) (B : J → Set V)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    Fintype.card J ≤ (Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)).card + A.card := by
  classical
  let E : Finset J := Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)
  let Q := Finset.univ \ E
  have hex : ∀ j : ↥Q, ∃ v : ↥A, v.val ∈ B j.val := by
    intro j
    have hn : ¬Disjoint (↑A : Set V) (B j.val) := by
      intro h
      exact (Finset.mem_sdiff.mp j.property).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    by_contra hh
    apply hn
    apply Set.disjoint_left.mpr
    intro v hv hvB
    exact hh ⟨⟨v, hv⟩, hvB⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hn
    exact Set.disjoint_left.mp (hdB i.val j.val (fun h => hn (Subtype.ext h)))
      (hf i) (hij ▸ hf j)
  have hQ : Q.card ≤ A.card := by simpa using Fintype.card_le_of_injective f hinj
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  simp only [Finset.card_univ] at hsum
  change Fintype.card J ≤ E.card + A.card
  dsimp [Q] at hQ
  omega

theorem rooting {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hh : 4 * A.card ≤ hadwigerNumber G) :
    Nonempty (RootedCliqueModel G (fun a : ↥A => a.val)) := by
  classical
  obtain ⟨B, hcB, hdB, heB⟩ := hasCliqueMinor_hadwigerNumber G
  let E : Finset (Fin (hadwigerNumber G)) :=
    Finset.univ.filter fun j => Disjoint (↑A : Set V) (B j)
  apply rooting_from_eligible G A (fun j : ↥E => B j.val) hc
  · exact fun j => hcB j.val
  · exact fun i j hij => hdB i.val j.val (fun h => hij (Subtype.ext h))
  · exact fun j => (Finset.mem_filter.mp j.property).2
  · exact fun i j hij => heB i.val j.val (fun h => hij (Subtype.ext h))
  · have hE := eligible_bags_card A B hdB
    simp only [Fintype.card_fin] at hE
    simp only [Fintype.card_coe]
    change hadwigerNumber G ≤ E.card + A.card at hE
    omega

end LinearListHadwiger

end OAI
