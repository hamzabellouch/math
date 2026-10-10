import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

structure BirthGraph (N : ℕ) where
  older : Fin N → Finset (Fin N)
  older_lt : ∀ v, ∀ u ∈ older v, u < v
  older_card : ∀ v, (older v).card ≤ 2

namespace BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def graph : SimpleGraph (Fin N) where
  Adj u v := u ∈ B.older v ∨ v ∈ B.older u
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun v h => by
    rcases h with h | h <;> exact (lt_irrefl v) (B.older_lt v v h)⟩

@[simp] theorem graph_adj (u v : Fin N) :
    B.graph.Adj u v ↔ u ∈ B.older v ∨ v ∈ B.older u := Iff.rfl

theorem graph_adj_of_lt {u v : Fin N} (huv : u < v) :
    B.graph.Adj u v ↔ u ∈ B.older v := by
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact False.elim ((not_lt_of_gt huv) (B.older_lt u v h))
  · exact Or.inl

def parentVertices (v : Fin N) : Finset (Fin N) := insert v (B.older v)

@[simp] theorem self_not_mem_older (v : Fin N) : v ∉ B.older v := by
  intro hv
  exact (lt_irrefl v) (B.older_lt v v hv)

theorem older_eq_pair {a b v : Fin N} (hab : a ≠ b)
    (ha : a ∈ B.older v) (hb : b ∈ B.older v) : B.older v = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro ha hb
  · simpa only [Finset.card_pair hab] using B.older_card v

theorem sorted_triangle {a b c : Fin N} (hab : a < b) (hbc : b < c)
    (hac : B.graph.Adj a c) (hbc' : B.graph.Adj b c) :
    B.parentVertices c = {a, b, c} := by
  have ho := B.older_eq_pair (ne_of_lt hab)
    ((B.graph_adj_of_lt (hab.trans hbc)).mp hac) ((B.graph_adj_of_lt hbc).mp hbc')
  simp only [parentVertices, ho]
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

section Labels
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (label : Fin N → V)

def parentType (v : Fin N) : Finset V := (B.parentVertices v).image label

def IsTriangle (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

def ExposedAt (v : Fin N) (T : Finset V) : Prop :=
  IsTriangle G T ∧
  (∃ u ∈ B.older v, label u ∈ T ∧ label v ∈ T) ∧
  ((B.older v).card = 2 → T ≠ B.parentType label v)

def ExtraEdge (a b : Fin N) : Prop :=
  a ≠ b ∧ ¬ B.graph.Adj a b ∧ G.Adj (label a) (label b)

theorem no_repeated_exposure (hinj : Function.Injective label)
    (hno : ∀ a b, ¬ B.ExtraEdge G label a b)
    {v w : Fin N} (hvw : v ≠ w) {T : Finset V}
    (hv : B.ExposedAt G label v T) (hw : B.ExposedAt G label w T) : False := by
  wlog hlt : w < v generalizing v w
  · exact this (Ne.symm hvw) hw hv (lt_of_le_of_ne (le_of_not_gt hlt) hvw)
  obtain ⟨k, hk, hkT, hwT⟩ := hw.2.1
  have hkw := B.older_lt w k hk
  have hvT := hv.2.1.choose_spec.2.2
  have hkv : k < v := hkw.trans hlt
  have hlabels : ({label k, label w, label v} : Finset V).card = 3 := by
    simp [hinj.ne (ne_of_lt hkw), hinj.ne (ne_of_lt hkv), hinj.ne (ne_of_lt hlt)]
  have hT : T = {label k, label w, label v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hkT, hwT, hvT⟩
    · rw [hlabels, hv.1.1]
  have hcv (u : Fin N) (hu : u < v) (huT : label u ∈ T) : u ∈ B.older v := by
    have hG : G.Adj (label u) (label v) := hv.1.2 _ huT _ hvT (hinj.ne (ne_of_lt hu))
    have hh : B.graph.Adj u v := by
      by_contra hn
      exact hno u v ⟨ne_of_lt hu, hn, hG⟩
    exact (B.graph_adj_of_lt hu).mp hh
  have hold := B.older_eq_pair (ne_of_lt hkw) (hcv k hkv hkT) (hcv w hlt hwT)
  have hcard : (B.older v).card = 2 := by rw [hold, Finset.card_pair (ne_of_lt hkw)]
  apply hv.2.2 hcard
  rw [parentType, parentVertices, hold, hT]
  ext x
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  aesop

structure SpawnRules : Prop where
  edge_labels : ∀ a b, B.graph.Adj a b → G.Adj (label a) (label b)
  attachment : ∀ v, (B.older v).card = 2 →
    ∀ a ∈ B.older v, ∀ b ∈ B.older v, a ≠ b → B.graph.Adj a b
  omit_parent : ∀ v p, p ∈ B.older v → (∀ a ∈ B.older v, a ≤ p) →
    (B.older p).card = 2 → B.parentType label v ≠ B.parentType label p
  distinct_siblings : ∀ v w, (B.older v).card = 2 → B.older v = B.older w →
    label v = label w → v = w

theorem older_sorted_pair {v : Fin N} (hv : (B.older v).card = 2) :
    ∃ x y : Fin N, x < y ∧ B.older v = {x, y} := by
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hv
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact ⟨x, y, hlt, hset⟩
  · exact ⟨y, x, hgt, hset.trans (Finset.pair_comm x y)⟩

theorem first_label_repeat_extra (hrules : B.SpawnRules G label)
    {v w : Fin N} (hv : (B.older v).card = 2) (hw : w < v)
    (hvw : label v = label w) :
    ∃ a b : Fin N, a < v ∧ b < v ∧ B.ExtraEdge G label a b := by
  by_contra hextra
  have hno (a b : Fin N) (ha : a < v) (hb : b < v)
      (hne : a ≠ b) (hedge : G.Adj (label a) (label b)) : B.graph.Adj a b := by
    by_contra hn
    exact hextra ⟨a, b, ha, hb, hne, hn, hedge⟩
  obtain ⟨x, y, hxy, hset⟩ := B.older_sorted_pair hv
  have hx : x ∈ B.older v := by rw [hset]; simp
  have hy : y ∈ B.older v := by rw [hset]; simp
  have hxv := B.older_lt v x hx
  have hyv := B.older_lt v y hy
  have hxwG : G.Adj (label x) (label w) := by
    rw [← hvw]
    exact hrules.edge_labels x v (Or.inl hx)
  have hywG : G.Adj (label y) (label w) := by
    rw [← hvw]
    exact hrules.edge_labels y v (Or.inl hy)
  have hxw : x ≠ w := fun hh => hxwG.ne (congrArg label hh)
  have hyw : y ≠ w := fun hh => hywG.ne (congrArg label hh)
  have hxwB := hno x w hxv hw hxw hxwG
  have hywB := hno y w hyv hw hyw hywG
  have hxyB := hrules.attachment v hv x hx y hy (ne_of_lt hxy)
  rcases lt_or_gt_of_ne (Ne.symm hyw) with hwy | hyw'
  · have hold := B.older_eq_pair hxw ((B.graph_adj_of_lt hxy).mp hxyB)
      ((B.graph_adj_of_lt hwy).mp hywB.symm)
    have hcard : (B.older y).card = 2 := by rw [hold, Finset.card_pair hxw]
    have hmax : ∀ a ∈ B.older v, a ≤ y := by
      intro a ha
      rw [hset] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact le_of_lt hxy
      · exact le_rfl
    apply hrules.omit_parent v y hy hmax hcard
    simp only [parentType, parentVertices, hset, hold, Finset.image_insert,
      Finset.image_singleton, hvw]
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · have hold := B.older_eq_pair (ne_of_lt hxy)
      ((B.graph_adj_of_lt (hxy.trans hyw')).mp hxwB)
      ((B.graph_adj_of_lt hyw').mp hywB)
    have heq := hrules.distinct_siblings v w hv (hset.trans hold.symm) hvw
    exact (ne_of_lt hw) heq.symm

theorem first_label_repeat_injective_extra (hrules : B.SpawnRules G label)
    {v w : Fin N} (hv : (B.older v).card = 2) (hw : w < v)
    (hvw : label v = label w)
    (hinj : Set.InjOn label {u | u < v}) :
    ∃ a b : Fin N, a < v ∧ b < v ∧ B.ExtraEdge G label a b ∧
      Set.InjOn label {u | u < v} := by
  obtain ⟨a, b, ha, hb, he⟩ := B.first_label_repeat_extra G label hrules hv hw hvw
  exact ⟨a, b, ha, hb, he, hinj⟩

theorem exists_first_repeat (h : ¬ Function.Injective label) :
    ∃ v w : Fin N, w < v ∧ label v = label w ∧ Set.InjOn label (Set.Iio v) := by
  classical
  let bad : Finset (Fin N) := Finset.univ.filter (fun v => ∃ w < v, label v = label w)
  have hbad (v : Fin N) : v ∈ bad ↔ ∃ w < v, label v = label w := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : bad.Nonempty := by
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp h
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨b, (hbad b).mpr ⟨a, hlt, hab.symm⟩⟩
    · exact ⟨a, (hbad a).mpr ⟨b, hgt, hab⟩⟩
  let v := bad.min' hne
  obtain ⟨w, hw, hvw⟩ := (hbad v).mp (Finset.min'_mem bad hne)
  refine ⟨v, w, hw, hvw, ?_⟩
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hm := Finset.min'_le bad b ((hbad b).mpr ⟨a, hlt, hab.symm⟩)
    exact (not_le_of_gt hb) hm
  · have hm := Finset.min'_le bad a ((hbad a).mpr ⟨b, hgt, hab⟩)
    exact (not_le_of_gt ha) hm

theorem exposed_collision_witness (hrules : B.SpawnRules G label)
    (R : ℕ) (hroots : Set.InjOn label {v : Fin N | v.val < R})
    (hnonroot : ∀ v : Fin N, R ≤ v.val → (B.older v).card = 2)
    {v w : Fin N} (hne : v ≠ w) {T : Finset V}
    (hv : B.ExposedAt G label v T) (hw : B.ExposedAt G label w T) :
    ∃ S : Set (Fin N), IsLowerSet S ∧ Set.InjOn label S ∧
      ∃ a ∈ S, ∃ b ∈ S, B.ExtraEdge G label a b := by
  classical
  by_cases hinj : Function.Injective label
  · have hex : ∃ a b, B.ExtraEdge G label a b := by
      by_contra hn
      have hno : ∀ a b, ¬ B.ExtraEdge G label a b := by simpa only [not_exists] using hn
      exact B.no_repeated_exposure G label hinj hno hne hv hw
    obtain ⟨a, b, he⟩ := hex
    exact ⟨Set.univ, isLowerSet_univ, hinj.injOn, a, Set.mem_univ _, b, Set.mem_univ _, he⟩
  · obtain ⟨z, u, huz, hzu, hpre⟩ := exists_first_repeat label hinj
    have hz : R ≤ z.val := by
      by_contra hn
      have hzR : z.val < R := Nat.lt_of_not_ge hn
      have huR : u.val < R := lt_trans huz hzR
      have hueq := hroots hzR huR hzu
      exact (ne_of_lt huz) hueq.symm
    obtain ⟨a, b, ha, hb, he⟩ :=
      B.first_label_repeat_extra G label hrules (hnonroot z hz) huz hzu
    exact ⟨Set.Iio z, isLowerSet_Iio z, hpre, a, ha, b, hb, he⟩

end Labels
end BirthGraph
end SharpTerminalLeave

end

end OAI
