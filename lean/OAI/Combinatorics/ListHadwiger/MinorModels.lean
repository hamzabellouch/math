import OAI.Combinatorics.ListHadwiger.Routing

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking

namespace MinorModel
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

def expand (M : MinorModel G H) (S : Set W) : Set V :=
  {v | ∃ w ∈ S, v ∈ M.branch w}

lemma branch_subset_expand (M : MinorModel G H) {S : Set W} {w : W} (hw : w ∈ S) :
    M.branch w ⊆ M.expand S := fun _ hv => ⟨w, hw, hv⟩

lemma expand_connected (M : MinorModel G H) {S : Set W}
    (hS : (H.induce S).Connected) : (G.induce (M.expand S)).Connected := by
  have hsame (w : S) (a b : M.branch w.val) :
      (G.induce (M.expand S)).Reachable
        ⟨a.val, M.branch_subset_expand w.property a.property⟩
        ⟨b.val, M.branch_subset_expand w.property b.property⟩ :=
    ((M.connected w.val).preconnected a b).map
      (G.induceHomOfLE (M.branch_subset_expand w.property)).toHom
  have hwalk : ∀ {u v : S} (p : (H.induce S).Walk u v)
      (a : M.branch u.val) (b : M.branch v.val),
      (G.induce (M.expand S)).Reachable
        ⟨a.val, M.branch_subset_expand u.property a.property⟩
        ⟨b.val, M.branch_subset_expand v.property b.property⟩ := by
    intro u v p
    induction p with
    | nil => exact hsame _
    | @cons u v z hadj p ih =>
      intro a b
      obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hadj
      have hxy' : (G.induce (M.expand S)).Adj
          ⟨x, M.branch_subset_expand u.property hx⟩
          ⟨y, M.branch_subset_expand v.property hy⟩ := hxy
      exact (hsame u a ⟨x, hx⟩).trans (hxy'.reachable.trans (ih ⟨y, hy⟩ b))
  refine { preconnected := ?_, nonempty := ?_ }
  · intro a b
    obtain ⟨u, hu, hau⟩ := a.property
    obtain ⟨v, hv, hbv⟩ := b.property
    obtain ⟨p⟩ := hS.preconnected ⟨u, hu⟩ ⟨v, hv⟩
    exact hwalk p ⟨a.val, hau⟩ ⟨b.val, hbv⟩
  · obtain ⟨w⟩ := hS.nonempty
    obtain ⟨v⟩ := (M.connected w.val).nonempty
    exact ⟨⟨v.val, M.branch_subset_expand w.property v.property⟩⟩

lemma expand_disjoint (M : MinorModel G H) {S T : Set W} (hST : Disjoint S T) :
    Disjoint (M.expand S) (M.expand T) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨a, ha, hva⟩ ⟨b, hb, hvb⟩
  by_cases hab : a = b
  · exact Set.disjoint_left.mp hST ha (hab ▸ hb)
  · exact Set.disjoint_left.mp (M.disjoint a b hab) hva hvb

theorem lift_clique (M : MinorModel G H) {t : ℕ} (h : HasCliqueMinor H t) :
    HasCliqueMinor G t := by
  obtain ⟨B, hc, hd, he⟩ := h
  refine ⟨fun i => M.expand (B i), fun i => M.expand_connected (hc i),
    fun i j hij => M.expand_disjoint (hd i j hij), ?_⟩
  intro i j hij
  obtain ⟨a, ha, b, hb, hab⟩ := he i j hij
  obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hab
  exact ⟨x, ⟨a, ha, hx⟩, y, ⟨b, hb, hy⟩, hxy⟩

theorem hadwiger_le [Fintype V] [Fintype W] (M : MinorModel G H) :
    hadwigerNumber H ≤ hadwigerNumber G :=
  cliqueMinor_le_hadwigerNumber (M.lift_clique (hasCliqueMinor_hadwigerNumber H))

end MinorModel

structure BagRouting {V I J : Type} (G : SimpleGraph V) (s : I → V)
    (B : J → Set V) where
  paths : ∀ i, Σ v, G.Path (s i) v
  bag : I → J
  bag_injective : Function.Injective bag
  endpoint_mem : ∀ i, (paths i).1 ∈ B (bag i)
  overlap : ∀ i j, i ≠ j → ∀ v,
    v ∈ (paths i).2.val.support → v ∈ (paths j).2.val.support →
      v = s i ∧ v = s j

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

noncomputable def totalLength [Fintype I] (D : BagRouting G s B) : ℕ :=
  ∑ i, (D.paths i).2.val.length

noncomputable def truncate [DecidableEq V] [DecidableEq I]
    (D : BagRouting G s B) (i : I) (j : J) (hj : j ∉ Set.range D.bag)
    (v : V) (hv : v ∈ (D.paths i).2.val.support) (hB : v ∈ B j) :
    BagRouting G s B := by
  classical
  let p : G.Path (s i) v :=
    ⟨(D.paths i).2.val.takeUntil v hv, (D.paths i).2.property.takeUntil hv⟩
  let paths : ∀ a, Σ w, G.Path (s a) w :=
    fun a => if h : a = i then h.symm ▸ (⟨v, p⟩ : Σ w, G.Path (s i) w) else D.paths a
  let f : I → J := Function.update D.bag i j
  refine ⟨paths, f, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact ha.trans hb.symm
    · subst a
      have h : j = D.bag b := by simpa [f, Function.update, hb] using hab
      exact (hj ⟨b, h.symm⟩).elim
    · subst b
      have h : D.bag a = j := by simpa [f, Function.update, ha] using hab
      exact (hj ⟨a, h⟩).elim
    · exact D.bag_injective (by simpa [f, Function.update, ha, hb] using hab)
  · intro a
    by_cases ha : a = i
    · subst a; simpa [paths, f, p] using hB
    · simpa [paths, f, ha] using D.endpoint_mem a
  · intro a b hab w hwa hwb
    have hsub (z : I) : (paths z).2.val.support ⊆ (D.paths z).2.val.support := by
      by_cases hz : z = i
      · subst z
        have heq : paths i = ⟨v, p⟩ := dite_eq_left rfl
        rw [heq]
        exact (D.paths i).2.val.support_takeUntil_subset_support hv
      · have heq : paths z = D.paths z := dite_eq_right hz
        rw [heq]
    exact D.overlap a b hab w (hsub a hwa) (hsub b hwb)

lemma truncate_length_lt [Fintype I] [DecidableEq V] [DecidableEq I]
    (D : BagRouting G s B) (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (i : I) (j : J) (hj : j ∉ Set.range D.bag)
    (v : V) (hv : v ∈ (D.paths i).2.val.support) (hB : v ∈ B j) :
    (D.truncate i j hj v hv hB).totalLength < D.totalLength := by
  classical
  have hne : v ≠ (D.paths i).1 := by
    intro heq
    have hx : j ≠ D.bag i := fun h => hj ⟨i, h.symm⟩
    exact Set.disjoint_left.mp (hdis j (D.bag i) hx) hB (heq ▸ D.endpoint_mem i)
  have hlt : ((D.paths i).2.val.takeUntil v hv).length < (D.paths i).2.val.length := by
    have hh := (D.paths i).2.val.length_takeUntil_le_length hv
    apply lt_of_le_of_ne hh
    intro heq
    have h := Walk.getVert_length_takeUntil hv
    rw [heq, Walk.getVert_length] at h
    exact hne h.symm
  have hi : (D.truncate i j hj v hv hB).paths i =
      ⟨v, ⟨(D.paths i).2.val.takeUntil v hv, (D.paths i).2.property.takeUntil hv⟩⟩ :=
    dite_eq_left rfl
  have ha : ∀ a, a ≠ i → (D.truncate i j hj v hv hB).paths a = D.paths a :=
    fun a h => dite_eq_right h
  apply Finset.sum_lt_sum
  · intro a _
    by_cases h : a = i
    · subst a
      rw [hi]
      exact hlt.le
    · rw [ha a h]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    exact hlt

theorem exists_avoiding_unused [Fintype I] [DecidableEq V] [DecidableEq I]
    (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (h : Nonempty (BagRouting G s B)) :
    ∃ D : BagRouting G s B, ∀ j, j ∉ Set.range D.bag →
      ∀ i v, v ∈ (D.paths i).2.val.support → v ∉ B j := by
  classical
  have hex : ∃ n : ℕ, ∃ D : BagRouting G s B, D.totalLength = n := by
    obtain ⟨D⟩ := h
    exact ⟨D.totalLength, D, rfl⟩
  obtain ⟨D, hd⟩ := Nat.find_spec hex
  refine ⟨D, ?_⟩
  intro j hj i v hv hB
  have hmin := Nat.find_min' hex ⟨D.truncate i j hj v hv hB, rfl⟩
  rw [← hd] at hmin
  exact (not_le_of_gt (D.truncate_length_lt hdis i j hj v hv hB)) hmin

end BagRouting

theorem bagRouting_of_double_packing {V J : Type} [Fintype V] [Fintype J]
    [DecidableEq V] (G : SimpleGraph V) (A : Finset V) (B : J → Set V)
    (hc : KConnectedOn G Finset.univ (2 * A.card))
    (hcB : ∀ j, (G.induce (B j)).Connected)
    (hdB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (haB : ∀ j, Disjoint (↑A : Set V) (B j))
    (hcard : 2 * A.card ≤ Fintype.card J) :
    Nonempty (BagRouting G (fun i : ↥A × Bool => i.1.val) B) := by
  classical
  have hex : ∀ j, ∃ v, v ∈ B j := fun j => by
    obtain ⟨v⟩ := (hcB j).nonempty
    exact ⟨v.val, v.property⟩
  choose rep hrep using hex
  have hinj : Function.Injective rep := by
    intro i j heq
    by_contra hij
    exact Set.disjoint_left.mp (hdB i j hij) (hrep i) (heq ▸ hrep j)
  let T : Finset V := Finset.univ.image rep
  have hAT : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro a ha ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact Set.disjoint_left.mp (haB j) ha (hrep j)
  have hT : T.card = Fintype.card J := by
    simp [T, Finset.card_image_of_injective _ hinj]
  obtain ⟨D⟩ := double_packing G A T hAT hc (hT ▸ hcard)
  have htar : ∀ i : ↥A × Bool, ∃ j, rep j = (D.target i).val := by
    intro i
    obtain ⟨j, _, heq⟩ := Finset.mem_image.mp (D.target i).property
    exact ⟨j, heq⟩
  choose idx hidx using htar
  refine ⟨⟨fun i => ⟨(D.target i).val, D.route i⟩, idx, ?_, ?_, D.overlap⟩⟩
  · intro i j hij
    apply D.target_injective
    apply Subtype.ext
    rw [← hidx i, ← hidx j, hij]
  · intro i
    change (D.target i).val ∈ B (idx i)
    rw [← hidx]
    exact hrep (idx i)

open scoped Classical

lemma exists_region_avoiding {V I : Type} [Fintype I] [DecidableEq V]
    (C : I → Set V) (X : Finset V) (c r : ℕ) (hc : 0 < c)
    (hI : c * r ≤ Fintype.card I) (hX : X.card < r)
    (hcon : ∀ v ∈ X, (Finset.univ.filter fun i => v ∈ C i).card ≤ c) :
    ∃ i, ∀ v ∈ C i, v ∉ X := by
  classical
  let met : Finset I := X.biUnion fun v => Finset.univ.filter fun i => v ∈ C i
  have hmet : met.card ≤ X.card * c := by
    calc
      met.card ≤ ∑ v ∈ X, (Finset.univ.filter fun i => v ∈ C i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ X, c := Finset.sum_le_sum hcon
      _ = X.card * c := by simp
  have hmI : met.card < Fintype.card I := by
    have hmul := Nat.mul_lt_mul_of_pos_right hX hc
    nlinarith
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show met.card < (Finset.univ : Finset I).card by simpa using hmI)
  refine ⟨i, ?_⟩
  intro v hv hvX
  exact hi (Finset.mem_biUnion.mpr ⟨v, hvX, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)

structure RootedCliqueModel {V I : Type} (G : SimpleGraph V) (roots : I → V) where
  branch : I → Set V
  connected : ∀ i, (G.induce (branch i)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  adjacent : ∀ i j, i ≠ j → ∃ x ∈ branch i, ∃ y ∈ branch j, G.Adj x y
  root_mem : ∀ i, roots i ∈ branch i

theorem rootedModel_of_packing {V W : Type} [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (M : MinorModel G H)
    {A B : Finset W} (D : FullPacking H A B)
    (hcl : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → H.Adj x y)
    (roots : ↥A → V) (hr : ∀ a, roots a ∈ M.branch a.val) :
    Nonempty (RootedCliqueModel G roots) := by
  let S : ↥A → Set W := fun a => {w | w ∈ (D.route a).val.support}
  refine ⟨⟨fun a => M.expand (S a), ?_, ?_, ?_, ?_⟩⟩
  · intro a
    exact M.expand_connected (D.route a).val.connected_induce_support
  · intro a b hab
    exact M.expand_disjoint (D.disjoint a b hab)
  · intro a b hab
    have hne : (D.target a).val ≠ (D.target b).val := by
      intro h
      exact hab (D.target_injective (Subtype.ext h))
    obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent
      (hcl _ (D.target a).property _ (D.target b).property hne)
    exact ⟨x, ⟨_, (D.route a).val.end_mem_support, hx⟩,
      y, ⟨_, (D.route b).val.end_mem_support, hy⟩, hxy⟩
  · intro a
    exact ⟨a.val, (D.route a).val.start_mem_support, hr a⟩

end LinearListHadwiger

end OAI
