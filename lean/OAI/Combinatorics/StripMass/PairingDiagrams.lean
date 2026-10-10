import Mathlib
import OAI.Combinatorics.StripMass.PfaffianMatrices

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset

 
def IsPairing {n : ℕ} (s : Finset (Fin n × Fin n)) : Prop :=
  (∀ e ∈ s, e.1 < e.2) ∧
  (∀ e ∈ s, ∀ f ∈ s, e = f ∨
    (e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)) ∧
  (∀ e ∈ s, ∀ f ∈ s, ¬(e.1 < f.1 ∧ f.1 < e.2 ∧ e.2 < f.2))

abbrev Pairing (n : ℕ) := {s : Finset (Fin n × Fin n) // IsPairing s}

instance (n : ℕ) : Fintype (Pairing n) := by classical exact Subtype.fintype _
instance (n : ℕ) : DecidableEq (Pairing n) := by classical infer_instance

def empty (n : ℕ) : Pairing n := ⟨∅, by simp [IsPairing]⟩

def Pairing.Adj {n : ℕ} (p : Pairing n) (i j : Fin n) : Prop :=
  (i,j) ∈ p.val ∨ (j,i) ∈ p.val

def Pairing.Occupied {n : ℕ} (p : Pairing n) (i : Fin n) : Prop :=
  ∃ j, p.Adj i j

@[simp] theorem empty_not_adj {n : ℕ} (i j : Fin n) : ¬ (empty n).Adj i j := by
  simp [Pairing.Adj, empty]
@[simp] theorem empty_not_occupied {n : ℕ} (i : Fin n) : ¬ (empty n).Occupied i := by
  simp [Pairing.Occupied]

theorem Pairing.adj_irrefl {n : ℕ} (p : Pairing n) (i : Fin n) : ¬p.Adj i i := by
  rintro (h | h) <;> exact (lt_irrefl i) (p.property.1 _ h)

theorem Pairing.eq_empty_iff {n : ℕ} (p : Pairing n) : p = empty n ↔ ∀ i, ¬p.Occupied i := by
  constructor
  · rintro rfl; simp
  · intro h
    apply Subtype.ext
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact h e.1 ⟨e.2, Or.inl he⟩

inductive Tile where
  | vacant | vertical₀ | vertical₁ | diagonal₀ | diagonal₁
  | cap | cup | verticalPair | capCup
  deriving DecidableEq

instance : Fintype Tile :=
  ⟨{.vacant, .vertical₀, .vertical₁, .diagonal₀, .diagonal₁, .cap, .cup,
    .verticalPair, .capCup}, by intro t; cases t <;> simp⟩

def Tile.edges : Tile → Finset (Fin 4 × Fin 4)
  | .vacant => ∅
  | .vertical₀ => {(0,2)}
  | .vertical₁ => {(1,3)}
  | .diagonal₀ => {(0,3)}
  | .diagonal₁ => {(1,2)}
  | .cap => {(0,1)}
  | .cup => {(2,3)}
  | .verticalPair => {(0,2),(1,3)}
  | .capCup => {(0,1),(2,3)}

def Tile.Adj (t : Tile) (i j : Fin 4) : Prop := (i,j) ∈ t.edges ∨ (j,i) ∈ t.edges

def Tile.Occupied (t : Tile) (i : Fin 4) : Prop := ∃ j, t.Adj i j

@[simp] theorem Tile.vacant_not_adj (i j : Fin 4) : ¬ Tile.vacant.Adj i j := by
  simp [Tile.Adj, Tile.edges]
@[simp] theorem Tile.vacant_not_occupied (i : Fin 4) : ¬ Tile.vacant.Occupied i := by
  simp [Tile.Occupied]

theorem Tile.eq_vacant_iff (t : Tile) : t = .vacant ↔ ∀ i, ¬t.Occupied i := by
  cases t <;> simp [Tile.Occupied, Tile.Adj, Tile.edges, Fin.forall_fin_succ]

 
structure Weights (𝕜 : Type*) where
  A : 𝕜
  B : 𝕜
  U : 𝕜
  E : 𝕜
  F : 𝕜

def Weights.tile {𝕜 : Type*} [One 𝕜] (w : Weights 𝕜) : Tile → 𝕜
  | .vacant => 1
  | .vertical₀ | .vertical₁ => w.A
  | .diagonal₀ | .diagonal₁ => w.B
  | .cap | .cup => w.U
  | .verticalPair => w.E
  | .capCup => w.F

abbrev Vertex (n : ℕ) := Fin n × Fin 4
abbrev Configuration (n : ℕ) := Fin n → Tile

 

def Wiring {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) : Prop :=
  (v.1 = w.1 ∧ (t v.1).Adj v.2 w.2) ∨
  (v.2 = 1 ∧ w.2 = 1 ∧ p.Adj v.1 w.1) ∨
  (v.2 = 3 ∧ w.2 = 0 ∧ v.1.val + 1 = w.1.val ∧ (t v.1).Occupied 3) ∨
  (w.2 = 3 ∧ v.2 = 0 ∧ w.1.val + 1 = v.1.val ∧ (t w.1).Occupied 3)

def Reach {n : ℕ} (p : Pairing n) (t : Configuration n) :=
  Relation.ReflTransGen (Wiring p t)

 

structure Realizes {n : ℕ} (p q : Pairing n) (t : Configuration n) : Prop where
  west : ∀ i, (t i).Occupied 1 ↔ p.Occupied i
  east : ∀ i, (t i).Occupied 2 ↔ q.Occupied i
  south : ∀ i, i.val = 0 → ¬ (t i).Occupied 0
  north : ∀ i, i.val + 1 = n → ¬ (t i).Occupied 3
  glued : ∀ i j, i.val + 1 = j.val → ((t i).Occupied 3 ↔ (t j).Occupied 0)
  no_loop : ∀ v w, Wiring p t v w → ∃ j, q.Occupied j ∧ Reach p t v (j,2)
  output : ∀ i j, i ≠ j → (q.Adj i j ↔ Reach p t (i,2) (j,2))

 

def column {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) :
    Matrix (Pairing n) (Pairing n) 𝕜 := by
  classical
  exact fun q p => ∑ t : Configuration n,
    if Realizes p q t then ∏ i, (w i).tile (t i) else 0

 
def identityWeights {𝕜 : Type*} [Zero 𝕜] [One 𝕜] : Weights 𝕜 := ⟨1,0,0,1,0⟩
def deletionWeights {𝕜 : Type*} [Zero 𝕜] [One 𝕜] : Weights 𝕜 := ⟨0,0,1,0,1⟩

def lambda : ℝ := Real.pi / 8
def L (u : ℝ) : ℝ := Real.sin (2 * lambda + u) * Real.sin (3 * lambda + u)
def physicalWeights (u : ℝ) : Weights ℝ :=
  let d := Real.cos (2 * lambda)
  ⟨d * Real.sin (3 * lambda - u) / L u,
   Real.sin u * Real.sin (3 * lambda - u) / L u,
   d * Real.sin u / L u,
   Real.sin (3 * lambda - u) * Real.sin (2 * lambda - u) / L u,
   Real.sin (u - lambda) * Real.sin u / L u⟩

def transfer {n : ℕ} (u : Fin n → ℝ) : Matrix (Pairing n) (Pairing n) ℝ :=
  column (fun i => physicalWeights (3 * lambda - u i))

 
abbrev NonemptyPairing (n : ℕ) := {p : Pairing n // p ≠ empty n}

def restrictedColumn {𝕜 : Type*} [CommRing 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) :
    Matrix (NonemptyPairing n) (NonemptyPairing n) 𝕜 :=
  (column w).submatrix Subtype.val Subtype.val

 
def VacuumRegular {𝕜 : Type*} [Field 𝕜] {n : ℕ} (w : Fin n → Weights 𝕜) : Prop :=
  (1 - restrictedColumn w).det ≠ 0

 
theorem realizes_empty_iff {n : ℕ} (p : Pairing n) (t : Configuration n) :
    Realizes p (empty n) t ↔ p = empty n ∧ t = fun _ => Tile.vacant := by
  constructor
  · intro h
    have ht : ∀ i, t i = .vacant := by
      intro i
      apply (Tile.eq_vacant_iff _).2
      intro a ⟨b, hab⟩
      obtain ⟨j, hj, _⟩ := h.no_loop (i,a) (i,b) (Or.inl ⟨rfl, hab⟩)
      exact empty_not_occupied j hj
    refine ⟨(Pairing.eq_empty_iff _).2 ?_, funext ht⟩
    intro i hi
    have := (h.west i).2 hi
    simp [ht i] at this
  · rintro ⟨rfl, rfl⟩
    have hw : ∀ v w : Vertex n, ¬ Wiring (empty n) (fun _ => Tile.vacant) v w := by
      intro v w
      simp [Wiring]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; simp
    · intro i; simp
    · intro i _; simp
    · intro i _; simp
    · intro i j _; simp
    · intro v w h; exact (hw v w h).elim
    · intro i j hij
      have hr : Reach (empty n) (fun _ : Fin n => Tile.vacant) (i,2) (j,2) ↔
          (j, (2 : Fin 4)) = (i,2) := Relation.reflTransGen_iff_eq (hw (i,2))
      simp [hr, Ne.symm hij]

theorem column_empty_row {𝕜 : Type*} [CommRing 𝕜] {n : ℕ}
    (w : Fin n → Weights 𝕜) (p : Pairing n) :
    column w (empty n) p = if p = empty n then 1 else 0 := by
  classical
  by_cases hp : p = empty n
  · subst p
    simp [column, realizes_empty_iff, Weights.tile]
  · simp [column, realizes_empty_iff, hp]

namespace Pairing

def map {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) : Pairing m := by
  classical
  refine ⟨p.val.map (f.toEmbedding.prodMap f.toEmbedding), ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    exact f.strictMono (p.property.1 a ha)
  · intro e he g hg
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    rcases Finset.mem_map.mp hg with ⟨b, hb, hgq⟩
    subst g
    rcases p.property.2.1 a ha b hb with h | ⟨h₁,h₂,h₃,h₄⟩
    · exact Or.inl (congrArg _ h)
    · exact Or.inr ⟨by simpa, by simpa, by simpa, by simpa⟩
  · intro e he g hg
    rcases Finset.mem_map.mp he with ⟨a, ha, heq⟩
    subst e
    rcases Finset.mem_map.mp hg with ⟨b, hb, hgq⟩
    subst g
    simpa using p.property.2.2 a ha b hb

def restrict {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m) : Pairing n := by
  classical
  refine ⟨p.val.preimage (fun e => (f e.1, f e.2))
    (f.toEmbedding.prodMap f.toEmbedding).injective.injOn, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    have h := p.property.1 _ (Finset.mem_preimage.mp he)
    simpa using h
  · intro e he g hg
    have h := p.property.2.1 _ (Finset.mem_preimage.mp he) _ (Finset.mem_preimage.mp hg)
    rcases h with h | ⟨h₁,h₂,h₃,h₄⟩
    · exact Or.inl <| Prod.ext (f.injective (congrArg Prod.fst h))
          (f.injective (congrArg Prod.snd h))
    · exact Or.inr ⟨fun h => h₁ (congrArg f h), fun h => h₂ (congrArg f h),
        fun h => h₃ (congrArg f h), fun h => h₄ (congrArg f h)⟩
  · intro e he g hg
    have h := p.property.2.2 _ (Finset.mem_preimage.mp he) _ (Finset.mem_preimage.mp hg)
    simpa using h

@[simp] theorem restrict_adj {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing m) (i j : Fin n) :
    (p.restrict f).Adj i j ↔ p.Adj (f i) (f j) := by
  classical
  exact or_congr
    (Finset.mem_preimage (hf := (f.toEmbedding.prodMap f.toEmbedding).injective.injOn))
    (Finset.mem_preimage (hf := (f.toEmbedding.prodMap f.toEmbedding).injective.injOn))

@[simp] theorem map_adj_image {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) (i j : Fin n) :
    (p.map f).Adj (f i) (f j) ↔ p.Adj i j := by
  classical
  simp [map, Adj, Finset.mem_map]

@[simp] theorem restrict_map {n m : ℕ} (f : Fin n ↪o Fin m) (p : Pairing n) :
    (p.map f).restrict f = p := by
  classical
  apply Subtype.ext
  ext e
  simp [restrict, map, Finset.mem_map]

 
def padBottom {n : ℕ} (p : Pairing n) : Pairing (n+1) := p.map (Fin.succOrderEmb n)

@[simp] theorem padBottom_adj_succ {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.padBottom.Adj i.succ j.succ ↔ p.Adj i j := map_adj_image _ _ _ _

@[simp] theorem padBottom_not_adj_zero {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padBottom.Adj 0 j := by
  classical
  simp [padBottom, map, Adj, Finset.mem_map]

@[simp] theorem padBottom_not_adj_zero' {n : ℕ} (p : Pairing n) (j : Fin (n+1)) :
    ¬ p.padBottom.Adj j 0 := by
  classical
  simp [padBottom, map, Adj, Finset.mem_map]

@[simp] theorem padBottom_not_occupied_zero {n : ℕ} (p : Pairing n) :
    ¬ p.padBottom.Occupied 0 := by
  simp [Occupied]

@[simp] theorem padBottom_occupied_succ {n : ℕ} (p : Pairing n) (i : Fin n) :
    p.padBottom.Occupied i.succ ↔ p.Occupied i := by
  simp only [Occupied, Fin.exists_fin_succ, padBottom_adj_succ, padBottom_not_adj_zero',
    false_or]

@[simp] theorem padBottom_empty {n : ℕ} : (empty n).padBottom = empty (n+1) := by
  classical
  apply Subtype.ext
  simp [padBottom, map, empty]

@[simp] theorem padBottom_eq_empty {n : ℕ} (p : Pairing n) :
    p.padBottom = empty (n+1) ↔ p = empty n := by
  simp only [eq_empty_iff, Fin.forall_fin_succ, padBottom_not_occupied_zero,
    padBottom_occupied_succ, not_false_eq_true, true_and]

 
theorem padBottom_restrict {n : ℕ} (p : Pairing (n+1)) (hp : ¬p.Occupied 0) :
    (p.restrict (Fin.succOrderEmb n)).padBottom = p := by
  classical
  apply Subtype.ext
  ext e
  rcases e with ⟨i,j⟩
  induction i using Fin.cases with
  | zero =>
      have hm : (0,j) ∉ p.val := fun h => hp ⟨j, Or.inl h⟩
      simp [padBottom, map, Finset.mem_map, hm]
  | succ i =>
      induction j using Fin.cases with
      | zero =>
          have hm : (i.succ,0) ∉ p.val := fun h => hp ⟨i.succ, Or.inr h⟩
          simp [padBottom, map, Finset.mem_map, hm]
      | succ j => simp [padBottom, map, restrict, Finset.mem_map]

def bottomVacantEquiv (n : ℕ) : Pairing n ≃ {p : Pairing (n+1) // ¬p.Occupied 0} where
  toFun p := ⟨p.padBottom, p.padBottom_not_occupied_zero⟩
  invFun p := p.val.restrict (Fin.succOrderEmb n)
  left_inv p := restrict_map _ p
  right_inv p := Subtype.ext <| padBottom_restrict p.val p.property

end Pairing

namespace Configuration

def padBottom {n : ℕ} (t : Configuration n) : Configuration (n+1) := Fin.cons .vacant t

@[simp] theorem padBottom_zero {n : ℕ} (t : Configuration n) : t.padBottom 0 = .vacant := rfl
@[simp] theorem padBottom_succ {n : ℕ} (t : Configuration n) (i : Fin n) :
    t.padBottom i.succ = t i := rfl

end Configuration

def vertexSucc {n : ℕ} (v : Vertex n) : Vertex (n+1) := (v.1.succ,v.2)

theorem vertexSucc_injective {n : ℕ} : Function.Injective (@vertexSucc n) := by
  intro v w h
  apply Prod.ext
  · exact Fin.succ_injective n (congrArg (fun v : Vertex (n+1) => v.1) h)
  · exact congrArg (fun v : Vertex (n+1) => v.2) h

theorem wiring_symm {n : ℕ} {p : Pairing n} {t : Configuration n} {v w : Vertex n}
    (h : Wiring p t v w) : Wiring p t w v := by
  rcases h with ⟨h,h'⟩ | ⟨h₁,h₂,h₃⟩ | h | h
  · left
    refine ⟨h.symm, ?_⟩
    simpa only [← h, Tile.Adj, or_comm] using h'
  · right; left
    exact ⟨h₂,h₁,h₃.elim Or.inr Or.inl⟩
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem reach_symm {n : ℕ} {p : Pairing n} {t : Configuration n} {v w : Vertex n}
    (h : Reach p t v w) : Reach p t w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h ih => exact (Relation.ReflTransGen.single (wiring_symm h)).trans ih

@[simp] theorem wiring_padBottom_zero {n : ℕ} (p : Pairing n) (t : Configuration n)
    (a : Fin 4) (w : Vertex (n+1)) :
    ¬Wiring p.padBottom t.padBottom (0,a) w := by
  simp [Wiring]

@[simp] theorem wiring_padBottom_zero_right {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v : Vertex (n+1)) (b : Fin 4) :
    ¬Wiring p.padBottom t.padBottom v (0,b) :=
  fun h => wiring_padBottom_zero p t b v (wiring_symm h)

@[simp] theorem wiring_padBottom_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Wiring p.padBottom t.padBottom (vertexSucc v) (vertexSucc w) ↔ Wiring p t v w := by
  simp [Wiring, vertexSucc, Nat.add_assoc]

theorem reach_padBottom_image {n : ℕ} (p : Pairing n) (t : Configuration n)
    {v : Vertex n} {w : Vertex (n+1)} (h : Reach p.padBottom t.padBottom (vertexSucc v) w) :
    ∃ z, w = vertexSucc z ∧ Reach p t v z := by
  induction h with
  | refl => exact ⟨v,rfl,Relation.ReflTransGen.refl⟩
  | @tail w z _ hwz ih =>
    obtain ⟨w',rfl,hw'⟩ := ih
    rcases z with ⟨j,b⟩
    induction j using Fin.cases with
    | zero => exact (wiring_padBottom_zero_right p t _ b hwz).elim
    | succ j =>
      exact ⟨(j,b),rfl,hw'.tail ((wiring_padBottom_iff p t _ _).1 hwz)⟩

@[simp] theorem reach_padBottom_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v w : Vertex n) :
    Reach p.padBottom t.padBottom (vertexSucc v) (vertexSucc w) ↔ Reach p t v w := by
  constructor
  · intro h
    obtain ⟨z,hz,hz'⟩ := reach_padBottom_image p t h
    have := vertexSucc_injective hz
    simpa only [this] using hz'
  · exact Relation.ReflTransGen.lift vertexSucc (fun a b h => (wiring_padBottom_iff p t a b).2 h) _ _

@[simp] theorem reach_padBottom_zero_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (a : Fin 4) (w : Vertex (n+1)) :
    Reach p.padBottom t.padBottom (0,a) w ↔ w = (0,a) :=
  Relation.reflTransGen_iff_eq (wiring_padBottom_zero p t a)

@[simp] theorem reach_padBottom_zero_right_iff {n : ℕ} (p : Pairing n) (t : Configuration n)
    (v : Vertex (n+1)) (b : Fin 4) :
    Reach p.padBottom t.padBottom v (0,b) ↔ v = (0,b) := by
  constructor
  · intro h
    exact (reach_padBottom_zero_iff p t b v).1 (reach_symm h)
  · rintro rfl; exact Relation.ReflTransGen.refl

 

end
end CriticalStrip.Diagram

end OAI
