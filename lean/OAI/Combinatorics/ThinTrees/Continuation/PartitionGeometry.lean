import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PartitionLattice
import OAI.Combinatorics.ThinTrees.RationalMatrix.SchurHistory

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

def block (p : Setoid V) (v : V) : Finset V := univ.filter (p v ·)

@[simp] lemma mem_block (p : Setoid V) (v w : V) : w ∈ block p v ↔ p v w := by
  simp [block]

lemma self_mem_block (p : Setoid V) (v : V) : v ∈ block p v :=
  (mem_block p v v).mpr (p.refl v)

lemma block_eq_iff (p : Setoid V) (v w : V) : block p v=block p w ↔ p v w := by
  constructor
  · intro he
    exact (mem_block p v w).mp (he ▸ self_mem_block p w)
  · intro h
    ext a
    simp only [mem_block]
    exact ⟨fun hv => p.trans (p.symm h) hv, fun hw => p.trans h hw⟩

lemma block_block (p : Setoid V) {a b v : V} (ha : a ∈ block p v) (hb : b ∈ block p v) :
    p a b := p.trans (p.symm ((mem_block _ _ _).mp ha)) ((mem_block _ _ _).mp hb)

lemma block_mono {p q : Setoid V} (hpq : p ≤ q) (v : V) : block p v ⊆ block q v := by
  intro w hw
  exact (mem_block _ _ _).mpr (hpq ((mem_block _ _ _).mp hw))

def parts (p : Setoid V) : Finset (Finset V) := univ.image (block p)

lemma block_mem_parts (p : Setoid V) (v : V) : block p v ∈ parts p :=
  mem_image.mpr ⟨v,mem_univ v,rfl⟩

lemma mem_parts (p : Setoid V) (A : Finset V) : A ∈ parts p ↔ ∃v, block p v=A := by
  simp [parts]

lemma parts_top [Nonempty V] : parts (⊤ : Setoid V)={univ} := by
  have hb (v : V) : block (⊤ : Setoid V) v=univ := by ext w; simp [block]
  unfold parts
  rw [show block (⊤ : Setoid V)=(fun _ => univ) from funext hb]
  exact image_const univ_nonempty _

lemma parts_disjoint (p : Setoid V) {A B : Finset V} (hA : A ∈ parts p)
    (hB : B ∈ parts p) (hAB : A ≠ B) : Disjoint A B := by
  obtain ⟨a,rfl⟩ := (mem_parts p A).mp hA
  obtain ⟨b,rfl⟩ := (mem_parts p B).mp hB
  apply disjoint_left.mpr
  intro v hva hvb
  apply hAB
  exact (block_eq_iff p a b).mpr
    (p.trans ((mem_block _ _ _).mp hva) (p.symm ((mem_block _ _ _).mp hvb)))

lemma parts_cover (p : Setoid V) : (parts p).biUnion id=univ := by
  apply eq_univ_of_forall
  intro v
  exact mem_biUnion.mpr ⟨block p v,block_mem_parts p v,self_mem_block p v⟩

lemma partCount_pos [Nonempty V] (p : Setoid V) : 0 < partCount p :=
  Fintype.card_pos_iff.mpr ⟨Quotient.mk p (Classical.arbitrary V)⟩

lemma partCount_top [Nonempty V] : partCount (⊤ : Setoid V)=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨Quotient.mk ⊤ (Classical.arbitrary V),?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y => exact Quotient.sound trivial

lemma two_le_partCount [Nonempty V] {p : Setoid V} (hp : p ≠ ⊤) : 2 ≤ partCount p := by
  have hh := partCount_strictAnti (lt_top_iff_ne_top.mpr hp)
  rw [partCount_top] at hh
  exact hh

variable {n m : ℕ}

lemma parts_partition (p : Setoid (Fin n)) : VertexPartition univ (parts p) := by
  refine ⟨?_,?_,?_⟩
  · intro A hA
    obtain ⟨v,rfl⟩ := (mem_parts p A).mp hA
    exact ⟨⟨v,self_mem_block p v⟩,subset_univ _⟩
  · intro A hA B hB hAB
    exact parts_disjoint p hA hB hAB
  · apply eq_univ_of_forall
    intro v
    exact mem_biUnion.mpr ⟨block p v,block_mem_parts p v,self_mem_block p v⟩

def toChain (f : ℕ → Setoid (Fin n)) (hf : Monotone f) : PartitionChain n where
  parts i := parts (f i)
  partition i := parts_partition (f i)
  coarsens i j hij A hA := by
    obtain ⟨v,rfl⟩ := (mem_parts (f i) A).mp hA
    exact ⟨block (f j) v,block_mem_parts _ _,block_mono (hf hij) v⟩

lemma toChain_block (f : ℕ → Setoid (Fin n)) (hf : Monotone f) (i : ℕ) (v : Fin n) :
    (toChain f hf).block i v=block (f i) v :=
  (toChain f hf).block_eq_of_mem (block_mem_parts _ _) (self_mem_block _ _)

def crossing (G : MultiGraph n m) (p : Setoid (Fin n)) : Finset (Fin m) :=
  univ.filter (fun e => ¬p (G.left e) (G.right e))

@[simp] lemma mem_crossing (G : MultiGraph n m) (p : Setoid (Fin n)) (e : Fin m) :
    e ∈ crossing G p ↔ ¬p (G.left e) (G.right e) := by simp [crossing]

lemma toChain_crossing (G : MultiGraph n m) (f : ℕ → Setoid (Fin n)) (hf : Monotone f) (i : ℕ) :
    (toChain f hf).crossing G i=crossing G (f i) := by
  ext e
  simp only [PartitionChain.mem_crossing,toChain_block,mem_crossing,block_eq_iff,ne_eq]

lemma capacity_eq_sum (G : MultiGraph n m) (w : Fin m → ℝ) (p : Setoid (Fin n)) :
    capacity G.left G.right w p=∑e ∈ crossing G p, w e := by
  simp only [capacity,crossing,sum_filter,crossingIndicator]
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp_all

lemma enumerate_chain (J : Finset (Setoid (Fin n)))
    (hJ : IsChain (· ≤ ·) (J : Set (Setoid (Fin n)))) :
    ∃f : ℕ → Setoid (Fin n), Monotone f ∧ f J.card=⊤ ∧
      (∀i, f i ∈ J ∨ f i=⊤) ∧ ∀p ∈ J, ∃i < J.card, f i=p := by
  let : LinearOrder J := hJ.lt_of_le.linearOrder
  let e : Fin J.card ≃o J := (univ : Finset J).orderIsoOfFin (by simp)
    |>.trans ((Set.orderIsoOfEq _ _ (Finset.coe_univ)).trans OrderIso.Set.univ)
  let f (i : ℕ) : Setoid (Fin n) := if hi : i < J.card then (e ⟨i,hi⟩).val else ⊤
  refine ⟨f,?_,?_,?_,?_⟩
  · intro i j hij
    dsimp only [f]
    split_ifs with hi hj
    · exact e.monotone (show (⟨i,hi⟩ : Fin J.card) ≤ ⟨j,hj⟩ from hij)
    · exact le_top
    · omega
    · exact le_rfl
  · dsimp [f]
    rw [dite_eq_right (lt_irrefl _)]
  · intro i
    dsimp only [f]
    split_ifs with hi
    · exact Or.inl (e ⟨i,hi⟩).property
    · exact Or.inr rfl
  · intro p hp
    let j := e.symm ⟨p,hp⟩
    refine ⟨j.val,j.isLt,?_⟩
    dsimp only [f]
    rw [dite_eq_left j.isLt]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨p,hp⟩)

end
end AlgorithmicThinTrees.Partitions
end

end OAI
