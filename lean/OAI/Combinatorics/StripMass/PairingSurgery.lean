import Mathlib
import OAI.Combinatorics.StripMass.PairingDiagrams

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
theorem IsPairing.mono {n : ℕ} {s t : Finset (Fin n × Fin n)}
    (h : IsPairing s) (ht : t ⊆ s) : IsPairing t :=
  ⟨fun e he => h.1 e (ht he), fun e he f hf => h.2.1 e (ht he) f (ht hf),
    fun e he f hf => h.2.2 e (ht he) f (ht hf)⟩

namespace Pairing

@[symm] theorem adj_symm {n : ℕ} {p : Pairing n} {i j : Fin n}
    (h : p.Adj i j) : p.Adj j i := h.symm

theorem adj_unique {n : ℕ} {p : Pairing n} {i j k : Fin n}
    (h : p.Adj i j) (g : p.Adj i k) : j = k := by
  rcases h with h | h <;> rcases g with g | g
  · rcases p.property.2.1 _ h _ g with he | ⟨hne, _, _, _⟩
    · exact congrArg Prod.snd he
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, hne, _, _⟩
    · exact (congrArg Prod.snd he).trans (congrArg Prod.fst he)
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, _, hne, _⟩
    · exact (congrArg Prod.fst he).trans (congrArg Prod.snd he)
    · exact (hne rfl).elim
  · rcases p.property.2.1 _ h _ g with he | ⟨_, _, _, hne⟩
    · exact congrArg Prod.fst he
    · exact (hne rfl).elim

 
def Cross {α : Type*} [LinearOrder α] (a b c d : α) : Prop :=
  (a<c ∧ c<b ∧ b<d) ∨ (c<a ∧ a<d ∧ d<b) ∨
  (b<c ∧ c<a ∧ a<d) ∨ (c<b ∧ b<d ∧ d<a) ∨
  (a<d ∧ d<b ∧ b<c) ∨ (d<a ∧ a<c ∧ c<b) ∨
  (b<d ∧ d<a ∧ a<c) ∨ (d<b ∧ b<c ∧ c<a)

theorem not_cross {n : ℕ} {p : Pairing n} {a b c d : Fin n}
    (h : p.Adj a b) (g : p.Adj c d) : ¬ Cross a b c d := by
  rcases h with h | h <;> rcases g with g | g
  all_goals
    have hp := p.property.1 _ h
    have hq := p.property.1 _ g
    have hx := p.property.2.2 _ h _ g
    have hy := p.property.2.2 _ g _ h
    dsimp only at hp hq hx hy
    simp only [Cross]
    omega

 
def omitTwo {n : ℕ} (p : Pairing n) (a b : Fin n) : Pairing n :=
  ⟨p.val.filter (fun e => e.1 ≠ a ∧ e.1 ≠ b ∧ e.2 ≠ a ∧ e.2 ≠ b),
    p.property.mono (filter_subset _ _)⟩

@[simp] theorem omitTwo_adj {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    (p.omitTwo a b).Adj i j ↔
      p.Adj i j ∧ i ≠ a ∧ i ≠ b ∧ j ≠ a ∧ j ≠ b := by
  simp only [Adj, omitTwo, mem_filter]
  tauto

theorem not_cross_iff_between {n : ℕ} {a b c d : Fin n}
    (hcd : c < d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ¬ Cross a b c d ↔ ((c<a ∧ a<d) ↔ (c<b ∧ b<d)) := by
  simp only [Cross]
  omega

 

theorem cap_no_cross {n : ℕ} {a b x y c d : Fin n}
    (hab : a.val + 1 = b.val) (hcd : c < d) (hc : c ≠ a) (hcb : c ≠ b)
    (hd : d ≠ a) (hdb : d ≠ b)
    (hxc : x ≠ c) (hxd : x ≠ d) (hyc : y ≠ c) (hyd : y ≠ d)
    (hx : ¬ Cross a x c d) (hy : ¬ Cross b y c d) : ¬ Cross x y c d := by
  apply (not_cross_iff_between hcd hxc hxd hyc hyd).mpr
  have hx' := (not_cross_iff_between hcd hc.symm hd.symm hxc hxd).mp hx
  have hy' := (not_cross_iff_between hcd hcb.symm hdb.symm hyc hyd).mp hy
  have h : (c<a ∧ a<d) ↔ (c<b ∧ b<d) := by omega
  exact hx'.symm.trans (h.trans hy')

def orderedEdge {n : ℕ} (x y : Fin n) : Fin n × Fin n := (min x y, max x y)

theorem orderedEdge_lt {n : ℕ} {x y : Fin n} (h : x ≠ y) :
    (orderedEdge x y).1 < (orderedEdge x y).2 := by
  simp only [orderedEdge, min_def, max_def]
  split_ifs <;> omega

theorem occupied_of_mem {n : ℕ} {p : Pairing n} {e : Fin n × Fin n}
    (h : e ∈ p.val) : p.Occupied e.1 ∧ p.Occupied e.2 :=
  ⟨⟨e.2, Or.inl h⟩, ⟨e.1, Or.inr h⟩⟩

theorem cap_new_edge_disjoint {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hx : p.Adj a x) (hy : p.Adj b y) {e : Fin n × Fin n}
    (he : e ∈ (p.omitTwo a b).val) :
    x ≠ e.1 ∧ x ≠ e.2 ∧ y ≠ e.1 ∧ y ≠ e.2 := by
  have hij : (p.omitTwo a b).Adj e.1 e.2 := Or.inl he
  obtain ⟨he',hca,hcb,hda,hdb⟩ := (omitTwo_adj p a b _ _).mp hij
  refine ⟨?_,?_,?_,?_⟩
  · rintro rfl
    exact hda (adj_unique he' (adj_symm hx))
  · rintro rfl
    exact hca (adj_unique (adj_symm he') (adj_symm hx))
  · rintro rfl
    exact hdb (adj_unique he' (adj_symm hy))
  · rintro rfl
    exact hcb (adj_unique (adj_symm he') (adj_symm hy))

 

def capSplice {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val + 1 = b.val) (hx : p.Adj a x) (hy : p.Adj b y)
    (hxy : x ≠ y) : Pairing n := by
  refine ⟨insert (orderedEdge x y) (p.omitTwo a b).val, ?_⟩
  refine ⟨?_,?_,?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact orderedEdge_lt hxy
    · exact (p.omitTwo a b).property.1 _ he
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;>
      rcases mem_insert.mp hf with rfl | hf
    · exact Or.inl rfl
    · right
      have hh := cap_new_edge_disjoint hx hy hf
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> tauto
    · right
      have hh := cap_new_edge_disjoint hx hy he
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> tauto
    · exact (p.omitTwo a b).property.2.1 _ he _ hf
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;>
      rcases mem_insert.mp hf with rfl | hf
    · simp
    · have hd := cap_new_edge_disjoint hx hy hf
      have hh := (omitTwo_adj p a b _ _).mp (Or.inl hf)
      have hc := cap_no_cross hab ((p.omitTwo a b).property.1 _ hf) hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 (not_cross hx hh.1) (not_cross hy hh.1)
      simp only [Cross] at hc
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> omega
    · have hd := cap_new_edge_disjoint hx hy he
      have hh := (omitTwo_adj p a b _ _).mp (Or.inl he)
      have hc := cap_no_cross hab ((p.omitTwo a b).property.1 _ he) hh.2.1 hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2
        hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 (not_cross hx hh.1) (not_cross hy hh.1)
      simp only [Cross] at hc
      simp only [orderedEdge, min_def, max_def]
      split_ifs <;> omega
    · exact (p.omitTwo a b).property.2.2 _ he _ hf


 

 


 

def mapOccupied {n m : ℕ} (p : Pairing n) (f : Fin n ↪ Fin m)
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i < j)) : Pairing m := by
  refine ⟨p.val.map (f.prodMap f), ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    apply (hf _ _ (occupied_of_mem ha).1 (occupied_of_mem ha).2).mpr
    exact p.property.1 _ ha
  · intro e he g hg
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    obtain ⟨b,hb,hgq⟩ := mem_map.mp hg
    subst g
    rcases p.property.2.1 _ ha _ hb with rfl | hh
    · exact Or.inl rfl
    · right
      simpa using hh
  · intro e he g hg
    obtain ⟨a,ha,heq⟩ := mem_map.mp he
    subst e
    obtain ⟨b,hb,hgq⟩ := mem_map.mp hg
    subst g
    change ¬ (f a.1 < f b.1 ∧ f b.1 < f a.2 ∧ f a.2 < f b.2)
    rw [hf _ _ (occupied_of_mem ha).1 (occupied_of_mem hb).1,
      hf _ _ (occupied_of_mem hb).1 (occupied_of_mem ha).2,
      hf _ _ (occupied_of_mem ha).2 (occupied_of_mem hb).2]
    exact p.property.2.2 _ ha _ hb

@[simp] theorem mapOccupied_adj {n m : ℕ} (p : Pairing n) (f : Fin n ↪ Fin m)
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i < j))
    (i j : Fin n) : (mapOccupied p f hf).Adj (f i) (f j) ↔ p.Adj i j := by
  simp [Adj, mapOccupied]

theorem swap_adjacent_order {n : ℕ} {a b i j : Fin n}
    (hab : a.val+1=b.val) (hi : i ≠ b) (hj : j ≠ b) :
    Equiv.swap a b i < Equiv.swap a b j ↔ i<j := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

 
def moveIntoVacancy {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (hb : ¬ p.Occupied b) : Pairing n :=
  p.mapOccupied (Equiv.swap a b).toEmbedding (fun _ _ hi hj =>
    swap_adjacent_order hab (fun h => hb (h ▸ hi)) (fun h => hb (h ▸ hj)))

 

theorem swap_adjacent_order_lower {n : ℕ} {a b i j : Fin n}
    (hab : a.val+1=b.val) (hi : i ≠ a) (hj : j ≠ a) :
    Equiv.swap a b i < Equiv.swap a b j ↔ i<j := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

def moveIntoLowerVacancy {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) : Pairing n :=
  p.mapOccupied (Equiv.swap a b).toEmbedding (fun _ _ hi hj =>
    swap_adjacent_order_lower hab (fun h => ha (h ▸ hi)) (fun h => ha (h ▸ hj)))

 
def insertCup {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b) : Pairing n := by
  have hlt : a<b := by omega
  have havoid (e : Fin n × Fin n) (he : e ∈ p.val) :
      a ≠ e.1 ∧ a ≠ e.2 ∧ b ≠ e.1 ∧ b ≠ e.2 := by
    have hh := occupied_of_mem he
    exact ⟨fun h => ha (h ▸ hh.1), fun h => ha (h ▸ hh.2),
      fun h => hb (h ▸ hh.1), fun h => hb (h ▸ hh.2)⟩
  refine ⟨insert (a,b) p.val, ?_, ?_, ?_⟩
  · intro e he
    rcases mem_insert.mp he with rfl | he
    · exact hlt
    · exact p.property.1 _ he
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    · exact Or.inl rfl
    · exact Or.inr (havoid _ hf)
    · right
      have hh := havoid _ he
      dsimp only
      tauto
    · exact p.property.2.1 _ he _ hf
  · intro e he f hf
    rcases mem_insert.mp he with rfl | he <;> rcases mem_insert.mp hf with rfl | hf
    all_goals try dsimp only
    · omega
    · omega
    · omega
    · exact p.property.2.2 _ he _ hf


 

 


def partner {n : ℕ} (p : Pairing n) (i : Fin n) (hi : p.Occupied i) : Fin n :=
  Classical.choose hi

theorem partner_adj {n : ℕ} (p : Pairing n) (i : Fin n) (hi : p.Occupied i) :
    p.Adj i (p.partner i hi) := Classical.choose_spec hi

theorem adjacent_partners {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬ p.Adj a b) :
    x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ x ≠ y := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro rfl; exact p.adj_irrefl _ hx
  · rintro rfl; exact hn hx
  · rintro rfl; exact hn (adj_symm hy)
  · rintro rfl; exact p.adj_irrefl _ hy
  · rintro rfl
    have := adj_unique (adj_symm hx) (adj_symm hy)
    omega

@[simp] theorem capSplice_adj {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hxy : x ≠ y)
    (i j : Fin n) :
    (capSplice p a b x y hab hx hy hxy).Adj i j ↔
      (i=x ∧ j=y) ∨ (i=y ∧ j=x) ∨ (p.omitTwo a b).Adj i j := by
  simp only [Adj, capSplice, mem_insert, orderedEdge, min_def, max_def,
    Prod.mk.injEq]
  split_ifs <;> tauto

@[simp] theorem capSplice_occupied {n : ℕ} (p : Pairing n) (a b x y : Fin n)
    (hab : a.val+1=b.val) (hx : p.Adj a x) (hy : p.Adj b y) (hxy : x ≠ y)
    (i : Fin n) :
    (capSplice p a b x y hab hx hy hxy).Occupied i ↔
      i=x ∨ i=y ∨ (p.omitTwo a b).Occupied i := by
  simp only [Occupied, capSplice_adj]
  constructor
  · rintro ⟨j,(⟨h,_⟩|⟨h,_⟩|h)⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j,h⟩)
  · rintro (rfl|rfl|⟨j,h⟩)
    · exact ⟨y,Or.inl ⟨rfl,rfl⟩⟩
    · exact ⟨x,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · exact ⟨j,Or.inr (Or.inr h)⟩

@[simp] theorem omitTwo_not_occupied_left {n : ℕ} (p : Pairing n) (a b : Fin n) :
    ¬ (p.omitTwo a b).Occupied a := by simp [Occupied]

@[simp] theorem omitTwo_not_occupied_right {n : ℕ} (p : Pairing n) (a b : Fin n) :
    ¬ (p.omitTwo a b).Occupied b := by simp [Occupied]

 

def capRemove {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b) : Pairing n :=
  p.capSplice a b (p.partner a ha) (p.partner b hb) hab
    (p.partner_adj a ha) (p.partner_adj b hb)
    (adjacent_partners hab (p.partner_adj a ha) (p.partner_adj b hb) hn).2.2.2.2

theorem capRemove_vacant {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val)
    (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b) :
    ¬ (capRemove p a b hab ha hb hn).Occupied a ∧
    ¬ (capRemove p a b hab ha hb hn).Occupied b := by
  have h := adjacent_partners hab (p.partner_adj a ha) (p.partner_adj b hb) hn
  simp only [capRemove,capSplice_occupied,omitTwo_not_occupied_left,
    omitTwo_not_occupied_right,or_false,not_or]
  exact ⟨⟨h.1.symm,h.2.2.1.symm⟩,⟨h.2.1.symm,h.2.2.2.1.symm⟩⟩

 

def tileStep {n : ℕ} (p : Pairing n) (a b : Fin n) (hab : a.val+1=b.val) :
    Tile → Option (Pairing n)
  | .vacant => if ¬ p.Occupied a ∧ ¬ p.Occupied b then some p else none
  | .vertical₀ => if p.Occupied a ∧ ¬ p.Occupied b then some p else none
  | .vertical₁ => if ¬ p.Occupied a ∧ p.Occupied b then some p else none
  | .diagonal₀ => if h : p.Occupied a ∧ ¬ p.Occupied b then
      some (p.moveIntoVacancy a b hab h.2) else none
  | .diagonal₁ => if h : ¬ p.Occupied a ∧ p.Occupied b then
      some (p.moveIntoLowerVacancy a b hab h.1) else none
  | .cap => if ha : p.Occupied a then if hb : p.Occupied b then
      if hn : p.Adj a b then none else some (p.capRemove a b hab ha hb hn)
      else none else none
  | .cup => if h : ¬ p.Occupied a ∧ ¬ p.Occupied b then
      some (p.insertCup a b hab h.1 h.2) else none
  | .verticalPair => if p.Occupied a ∧ p.Occupied b then some p else none
  | .capCup => if ha : p.Occupied a then if hb : p.Occupied b then
      if hn : p.Adj a b then none else
        some ((p.capRemove a b hab ha hb hn).insertCup a b hab
          (capRemove_vacant p a b hab ha hb hn).1
          (capRemove_vacant p a b hab ha hb hn).2)
      else none else none

end Pairing
end
end CriticalStrip.Diagram

end OAI
