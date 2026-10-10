import Mathlib
import OAI.Combinatorics.StripMass.PatchReplacement
import OAI.Combinatorics.StripMass.PairingSurgery

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.CutPatch
noncomputable section
open Finset

inductive Shape where
  | vacant | single₀ | single₁ | paired | separate
  deriving DecidableEq

instance : Fintype Shape := ⟨{.vacant,.single₀,.single₁,.paired,.separate}, by intro s; cases s <;> simp⟩

def inputEdges : Shape → Finset (Fin 6 × Fin 6)
  | .vacant => ∅
  | .single₀ => {(0,4)}
  | .single₁ => {(1,5)}
  | .paired => {(0,1)}
  | .separate => {(0,4),(1,5)}

def tilePort (i : Fin 4) : Fin 6 := Fin.castLE (by decide) i

def Adj (a : Shape) (t : Tile) (v w : Fin 6) : Prop :=
  (v,w) ∈ inputEdges a ∨ (w,v) ∈ inputEdges a ∨
    ∃ i j : Fin 4, t.Adj i j ∧ v = tilePort i ∧ w = tilePort j

instance (a : Shape) (t : Tile) : DecidableRel (Adj a t) := fun _ _ => by
  unfold Adj; infer_instance

def inputOccupied (a : Shape) (i : Fin 2) : Prop :=
  ∃ j, (tilePort (Fin.castLE (by decide) i),j) ∈ inputEdges a ∨
    (j,tilePort (Fin.castLE (by decide) i)) ∈ inputEdges a

instance (a : Shape) (i : Fin 2) : Decidable (inputOccupied a i) := by
  unfold inputOccupied; infer_instance

def Compatible (a : Shape) (t : Tile) : Prop :=
  ∀ i : Fin 2, inputOccupied a i ↔ t.Occupied (Fin.castLE (by decide) i)

instance (a : Shape) (t : Tile) : Decidable (Compatible a t) := by
  unfold Compatible; infer_instance

def boundary : Fin 4 → Fin 6 := ![2,3,4,5]

def active (a : Shape) (t : Tile) (i : Fin 4) : Prop :=
  ∃ w, Adj a t (boundary i) w

instance (a : Shape) (t : Tile) (i : Fin 4) : Decidable (active a t i) := by
  unfold active; infer_instance

def boundaryAdj (d : Finset (Fin 4 × Fin 4)) (i j : Fin 4) : Prop :=
  (i,j) ∈ d ∨ (j,i) ∈ d

def boundarySupport (d : Finset (Fin 4 × Fin 4)) (i : Fin 4) : Prop :=
  ∃ j, boundaryAdj d i j

instance (d : Finset (Fin 4 × Fin 4)) (i j : Fin 4) : Decidable (boundaryAdj d i j) := by
  unfold boundaryAdj; infer_instance
instance (d : Finset (Fin 4 × Fin 4)) (i : Fin 4) : Decidable (boundarySupport d i) := by
  unfold boundarySupport; infer_instance

def profile : Shape → Tile → Option (Finset (Fin 4 × Fin 4))
  | .vacant, .vacant => some ∅
  | .vacant, .cup => some {(0,1)}
  | .single₀, .vertical₀ => some {(0,2)}
  | .single₀, .diagonal₀ => some {(1,2)}
  | .single₁, .vertical₁ => some {(1,3)}
  | .single₁, .diagonal₁ => some {(0,3)}
  | .paired, .verticalPair => some {(0,1)}
  | .separate, .cap => some {(2,3)}
  | .separate, .verticalPair => some {(0,2),(1,3)}
  | .separate, .capCup => some {(0,1),(2,3)}
  | _,_ => none

def rootTable : Shape → Tile → Fin 6 → Fin 6
  | .vacant, .vacant => ![0,1,2,3,4,5]
  | .vacant, .vertical₀ => ![0,1,0,3,4,5]
  | .vacant, .vertical₁ => ![0,1,2,1,4,5]
  | .vacant, .diagonal₀ => ![0,1,2,0,4,5]
  | .vacant, .diagonal₁ => ![0,1,1,3,4,5]
  | .vacant, .cap => ![0,0,2,3,4,5]
  | .vacant, .cup => ![0,1,2,2,4,5]
  | .vacant, .verticalPair => ![0,1,0,1,4,5]
  | .vacant, .capCup => ![0,0,2,2,4,5]
  | .single₀, .vacant => ![0,1,2,3,0,5]
  | .single₀, .vertical₀ => ![0,1,0,3,0,5]
  | .single₀, .vertical₁ => ![0,1,2,1,0,5]
  | .single₀, .diagonal₀ => ![0,1,2,0,0,5]
  | .single₀, .diagonal₁ => ![0,1,1,3,0,5]
  | .single₀, .cap => ![0,0,2,3,0,5]
  | .single₀, .cup => ![0,1,2,2,0,5]
  | .single₀, .verticalPair => ![0,1,0,1,0,5]
  | .single₀, .capCup => ![0,0,2,2,0,5]
  | .single₁, .vacant => ![0,1,2,3,4,1]
  | .single₁, .vertical₀ => ![0,1,0,3,4,1]
  | .single₁, .vertical₁ => ![0,1,2,1,4,1]
  | .single₁, .diagonal₀ => ![0,1,2,0,4,1]
  | .single₁, .diagonal₁ => ![0,1,1,3,4,1]
  | .single₁, .cap => ![0,0,2,3,4,0]
  | .single₁, .cup => ![0,1,2,2,4,1]
  | .single₁, .verticalPair => ![0,1,0,1,4,1]
  | .single₁, .capCup => ![0,0,2,2,4,0]
  | .paired, .vacant => ![0,0,2,3,4,5]
  | .paired, .vertical₀ => ![0,0,0,3,4,5]
  | .paired, .vertical₁ => ![0,0,2,0,4,5]
  | .paired, .diagonal₀ => ![0,0,2,0,4,5]
  | .paired, .diagonal₁ => ![0,0,0,3,4,5]
  | .paired, .cap => ![0,0,2,3,4,5]
  | .paired, .cup => ![0,0,2,2,4,5]
  | .paired, .verticalPair => ![0,0,0,0,4,5]
  | .paired, .capCup => ![0,0,2,2,4,5]
  | .separate, .vacant => ![0,1,2,3,0,1]
  | .separate, .vertical₀ => ![0,1,0,3,0,1]
  | .separate, .vertical₁ => ![0,1,2,1,0,1]
  | .separate, .diagonal₀ => ![0,1,2,0,0,1]
  | .separate, .diagonal₁ => ![0,1,1,3,0,1]
  | .separate, .cap => ![0,0,2,3,0,0]
  | .separate, .cup => ![0,1,2,2,0,1]
  | .separate, .verticalPair => ![0,1,0,1,0,1]
  | .separate, .capCup => ![0,0,2,2,0,0]

def parentTable : Shape → Tile → Fin 6 → Fin 6
  | .vacant, .vacant => ![0,1,2,3,4,5]
  | .vacant, .vertical₀ => ![0,1,0,3,4,5]
  | .vacant, .vertical₁ => ![0,1,2,1,4,5]
  | .vacant, .diagonal₀ => ![0,1,2,0,4,5]
  | .vacant, .diagonal₁ => ![0,1,1,3,4,5]
  | .vacant, .cap => ![0,0,2,3,4,5]
  | .vacant, .cup => ![0,1,2,2,4,5]
  | .vacant, .verticalPair => ![0,1,0,1,4,5]
  | .vacant, .capCup => ![0,0,2,2,4,5]
  | .single₀, .vacant => ![0,1,2,3,0,5]
  | .single₀, .vertical₀ => ![0,1,0,3,0,5]
  | .single₀, .vertical₁ => ![0,1,2,1,0,5]
  | .single₀, .diagonal₀ => ![0,1,2,0,0,5]
  | .single₀, .diagonal₁ => ![0,1,1,3,0,5]
  | .single₀, .cap => ![0,0,2,3,0,5]
  | .single₀, .cup => ![0,1,2,2,0,5]
  | .single₀, .verticalPair => ![0,1,0,1,0,5]
  | .single₀, .capCup => ![0,0,2,2,0,5]
  | .single₁, .vacant => ![0,1,2,3,4,1]
  | .single₁, .vertical₀ => ![0,1,0,3,4,1]
  | .single₁, .vertical₁ => ![0,1,2,1,4,1]
  | .single₁, .diagonal₀ => ![0,1,2,0,4,1]
  | .single₁, .diagonal₁ => ![0,1,1,3,4,1]
  | .single₁, .cap => ![0,0,2,3,4,1]
  | .single₁, .cup => ![0,1,2,2,4,1]
  | .single₁, .verticalPair => ![0,1,0,1,4,1]
  | .single₁, .capCup => ![0,0,2,2,4,1]
  | .paired, .vacant => ![0,0,2,3,4,5]
  | .paired, .vertical₀ => ![0,0,0,3,4,5]
  | .paired, .vertical₁ => ![0,0,2,1,4,5]
  | .paired, .diagonal₀ => ![0,0,2,0,4,5]
  | .paired, .diagonal₁ => ![0,0,1,3,4,5]
  | .paired, .cap => ![0,0,2,3,4,5]
  | .paired, .cup => ![0,0,2,2,4,5]
  | .paired, .verticalPair => ![0,0,0,1,4,5]
  | .paired, .capCup => ![0,0,2,2,4,5]
  | .separate, .vacant => ![0,1,2,3,0,1]
  | .separate, .vertical₀ => ![0,1,0,3,0,1]
  | .separate, .vertical₁ => ![0,1,2,1,0,1]
  | .separate, .diagonal₀ => ![0,1,2,0,0,1]
  | .separate, .diagonal₁ => ![0,1,1,3,0,1]
  | .separate, .cap => ![0,0,2,3,0,1]
  | .separate, .cup => ![0,1,2,2,0,1]
  | .separate, .verticalPair => ![0,1,0,1,0,1]
  | .separate, .capCup => ![0,0,2,2,0,1]

def rankTable : Shape → Tile → Fin 6 → ℕ
  | .vacant, .vacant => ![0,0,0,0,0,0]
  | .vacant, .vertical₀ => ![0,0,1,0,0,0]
  | .vacant, .vertical₁ => ![0,0,0,1,0,0]
  | .vacant, .diagonal₀ => ![0,0,0,1,0,0]
  | .vacant, .diagonal₁ => ![0,0,1,0,0,0]
  | .vacant, .cap => ![0,1,0,0,0,0]
  | .vacant, .cup => ![0,0,0,1,0,0]
  | .vacant, .verticalPair => ![0,0,1,1,0,0]
  | .vacant, .capCup => ![0,1,0,1,0,0]
  | .single₀, .vacant => ![0,0,0,0,1,0]
  | .single₀, .vertical₀ => ![0,0,1,0,1,0]
  | .single₀, .vertical₁ => ![0,0,0,1,1,0]
  | .single₀, .diagonal₀ => ![0,0,0,1,1,0]
  | .single₀, .diagonal₁ => ![0,0,1,0,1,0]
  | .single₀, .cap => ![0,1,0,0,1,0]
  | .single₀, .cup => ![0,0,0,1,1,0]
  | .single₀, .verticalPair => ![0,0,1,1,1,0]
  | .single₀, .capCup => ![0,1,0,1,1,0]
  | .single₁, .vacant => ![0,0,0,0,0,1]
  | .single₁, .vertical₀ => ![0,0,1,0,0,1]
  | .single₁, .vertical₁ => ![0,0,0,1,0,1]
  | .single₁, .diagonal₀ => ![0,0,0,1,0,1]
  | .single₁, .diagonal₁ => ![0,0,1,0,0,1]
  | .single₁, .cap => ![0,1,0,0,0,2]
  | .single₁, .cup => ![0,0,0,1,0,1]
  | .single₁, .verticalPair => ![0,0,1,1,0,1]
  | .single₁, .capCup => ![0,1,0,1,0,2]
  | .paired, .vacant => ![0,1,0,0,0,0]
  | .paired, .vertical₀ => ![0,1,1,0,0,0]
  | .paired, .vertical₁ => ![0,1,0,2,0,0]
  | .paired, .diagonal₀ => ![0,1,0,1,0,0]
  | .paired, .diagonal₁ => ![0,1,2,0,0,0]
  | .paired, .cap => ![0,1,0,0,0,0]
  | .paired, .cup => ![0,1,0,1,0,0]
  | .paired, .verticalPair => ![0,1,1,2,0,0]
  | .paired, .capCup => ![0,1,0,1,0,0]
  | .separate, .vacant => ![0,0,0,0,1,1]
  | .separate, .vertical₀ => ![0,0,1,0,1,1]
  | .separate, .vertical₁ => ![0,0,0,1,1,1]
  | .separate, .diagonal₀ => ![0,0,0,1,1,1]
  | .separate, .diagonal₁ => ![0,0,1,0,1,1]
  | .separate, .cap => ![0,1,0,0,1,2]
  | .separate, .cup => ![0,0,0,1,1,1]
  | .separate, .verticalPair => ![0,0,1,1,1,1]
  | .separate, .capCup => ![0,1,0,1,1,2]

def ForestConditions (a : Shape) (t : Tile) : Prop :=
  (∀ v w, Adj a t v w → rootTable a t v = rootTable a t w) ∧
  (∀ v, v ≠ rootTable a t v → Adj a t v (parentTable a t v)) ∧
  (∀ v, v ≠ rootTable a t v → rankTable a t (parentTable a t v) < rankTable a t v)

instance (a : Shape) (t : Tile) : Decidable (ForestConditions a t) := by
  unfold ForestConditions; infer_instance

theorem forestConditions (a : Shape) (t : Tile) : ForestConditions a t := by
  cases a <;> cases t <;> decide

def forest (a : Shape) (t : Tile) : ConnectivityCertificate (Adj a t) where
  root := rootTable a t
  parent := parentTable a t
  rank := rankTable a t
  edge_root := (forestConditions a t).1
  parent_edge := (forestConditions a t).2.1
  parent_rank := (forestConditions a t).2.2

theorem adj_symmetric (a : Shape) (t : Tile) : Std.Symm (Adj a t) := by
  constructor
  intro v w h
  rcases h with h | h | ⟨i,j,h,rfl,rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨j,i,h.symm,rfl,rfl⟩)

theorem reach_iff (a : Shape) (t : Tile) (v w : Fin 6) :
    Relation.ReflTransGen (Adj a t) v w ↔ rootTable a t v = rootTable a t w :=
  (forest a t).reach_iff (adj_symmetric a t) v w

def GoodChecks (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Prop :=
  Compatible a t ∧ (∀ i, active a t i ↔ boundarySupport d i) ∧
  (∀ v w, Adj a t v w → ∃ i, active a t i ∧ rootTable a t v = rootTable a t (boundary i)) ∧
  (∀ i j, i ≠ j → (boundaryAdj d i j ↔ rootTable a t (boundary i) = rootTable a t (boundary j)))

def BadChecks (a : Shape) (t : Tile) : Prop :=
  ¬ Compatible a t ∨ ∃ v w, Adj a t v w ∧
    ∀ i, active a t i → rootTable a t v ≠ rootTable a t (boundary i)

instance (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Decidable (GoodChecks a t d) := by
  unfold GoodChecks; infer_instance
instance (a : Shape) (t : Tile) : Decidable (BadChecks a t) := by
  unfold BadChecks; infer_instance

def ProfileChecks (a : Shape) (t : Tile) : Prop :=
  match profile a t with
  | some d => GoodChecks a t d
  | none => BadChecks a t

instance (a : Shape) (t : Tile) : Decidable (ProfileChecks a t) := by
  unfold ProfileChecks; split <;> infer_instance

theorem profileChecks (a : Shape) (t : Tile) : ProfileChecks a t := by
  cases a <;> cases t <;> decide

structure Realizes (a : Shape) (t : Tile) (d : Finset (Fin 4 × Fin 4)) : Prop where
  compatible : Compatible a t
  occupied : ∀ i, active a t i ↔ boundarySupport d i
  no_loop : ∀ v w, Adj a t v w → ∃ i, active a t i ∧ Relation.ReflTransGen (Adj a t) v (boundary i)
  output : ∀ i j, i ≠ j → (boundaryAdj d i j ↔ Relation.ReflTransGen (Adj a t) (boundary i) (boundary j))

theorem realizes_of_profile {a : Shape} {t : Tile} {d : Finset (Fin 4 × Fin 4)}
    (h : profile a t = some d) : Realizes a t d := by
  have hp := profileChecks a t
  simp only [ProfileChecks,h] at hp
  exact ⟨hp.1,hp.2.1,fun v w hvw => by
    obtain ⟨i,hi,he⟩ := hp.2.2.1 v w hvw
    exact ⟨i,hi,(reach_iff a t v (boundary i)).mpr he⟩,
    fun i j hij => (hp.2.2.2 i j hij).trans (reach_iff a t _ _).symm⟩

theorem none_has_closed {a : Shape} {t : Tile} (h : profile a t = none)
    (hc : Compatible a t) :
    ∃ v w, Adj a t v w ∧ ∀ i, active a t i → ¬ Relation.ReflTransGen (Adj a t) v (boundary i) := by
  have hp := profileChecks a t
  simp only [ProfileChecks,h] at hp
  rcases hp with hp | ⟨v,w,hvw,hout⟩
  · exact (hp hc).elim
  · exact ⟨v,w,hvw,fun i hi hh => hout i hi ((reach_iff a t _ _).mp hh)⟩

end
end CriticalStrip.Diagram.CutPatch

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical
namespace Pairing

def partnerOrSelf {n : ℕ} (p : Pairing n) (i : Fin n) : Fin n :=
  if h : p.Occupied i then p.partner i h else i

theorem adj_partnerOrSelf {n : ℕ} (p : Pairing n) (i j : Fin n) :
    p.Adj i j ↔ p.Occupied i ∧ j = p.partnerOrSelf i := by
  by_cases hi : p.Occupied i
  · simp only [partnerOrSelf,hi,dite_eq_left,true_and]
    exact ⟨fun h => adj_unique h (p.partner_adj i hi),fun h => h ▸ p.partner_adj i hi⟩
  · simp only [hi,false_and,iff_false]
    exact fun h => hi ⟨j,h⟩

theorem adj_omit_decomposition {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.Adj i j ↔ (p.omitTwo a b).Adj i j ∨
      (i=a ∧ p.Adj a j) ∨ (j=a ∧ p.Adj a i) ∨
      (i=b ∧ p.Adj b j) ∨ (j=b ∧ p.Adj b i) := by
  rw [omitTwo_adj]
  constructor
  · intro h
    by_cases hia : i=a
    · exact Or.inr (Or.inl ⟨hia,hia ▸ h⟩)
    by_cases hja : j=a
    · exact Or.inr (Or.inr (Or.inl ⟨hja,hja ▸ adj_symm h⟩))
    by_cases hib : i=b
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hib,hib ▸ h⟩)))
    by_cases hjb : j=b
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hjb,hjb ▸ adj_symm h⟩)))
    exact Or.inl ⟨h,hia,hib,hja,hjb⟩
  · rintro (⟨h,_⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩)
    · exact h
    · exact h
    · exact adj_symm h
    · exact h
    · exact adj_symm h

@[simp] theorem insertCup_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) (hb : ¬ p.Occupied b)
    (i j : Fin n) :
    (p.insertCup a b hab ha hb).Adj i j ↔
      (i=a ∧ j=b) ∨ (i=b ∧ j=a) ∨ p.Adj i j := by
  simp only [Adj,insertCup,mem_insert,Prod.mk.injEq]
  tauto

@[simp] theorem mapOccupied_equiv_adj {n : ℕ} (p : Pairing n) (f : Equiv.Perm (Fin n))
    (hf : ∀ i j, p.Occupied i → p.Occupied j → (f i < f j ↔ i<j))
    (i j : Fin n) :
    (p.mapOccupied f.toEmbedding hf).Adj i j ↔ p.Adj (f.symm i) (f.symm j) := by
  convert (mapOccupied_adj p f.toEmbedding hf (f.symm i) (f.symm j)) using 1
  simp

@[simp] theorem moveIntoVacancy_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (hb : ¬ p.Occupied b) (i j : Fin n) :
    (p.moveIntoVacancy a b hab hb).Adj i j ↔
      p.Adj (Equiv.swap a b i) (Equiv.swap a b j) := by
  exact mapOccupied_equiv_adj p (Equiv.swap a b) _ i j

@[simp] theorem moveIntoLowerVacancy_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : ¬ p.Occupied a) (i j : Fin n) :
    (p.moveIntoLowerVacancy a b hab ha).Adj i j ↔
      p.Adj (Equiv.swap a b i) (Equiv.swap a b j) := by
  exact mapOccupied_equiv_adj p (Equiv.swap a b) _ i j

@[simp] theorem capRemove_adj {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (ha : p.Occupied a) (hb : p.Occupied b) (hn : ¬ p.Adj a b)
    (i j : Fin n) :
    (p.capRemove a b hab ha hb hn).Adj i j ↔
      (i=p.partnerOrSelf a ∧ j=p.partnerOrSelf b) ∨
      (i=p.partnerOrSelf b ∧ j=p.partnerOrSelf a) ∨ (p.omitTwo a b).Adj i j := by
  simp only [capRemove,capSplice_adj,partnerOrSelf,ha,hb,dite_eq_left]

 
def cutShape {n : ℕ} (p : Pairing n) (a b : Fin n) : CutPatch.Shape :=
  if p.Occupied a then
    if p.Occupied b then if p.Adj a b then .paired else .separate else .single₀
  else if p.Occupied b then .single₁ else .vacant

 
def cutLabels {n : ℕ} (p : Pairing n) (a b : Fin n) : Fin 4 → Fin n :=
  ![a,b,p.partnerOrSelf a,p.partnerOrSelf b]

theorem tileStep_none_iff {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) :
    p.tileStep a b hab t = none ↔ CutPatch.profile (p.cutShape a b) t = none := by
  by_cases ha : p.Occupied a <;> by_cases hb : p.Occupied b <;>
    by_cases hn : p.Adj a b <;> cases t <;> simp [tileStep,cutShape,ha,hb,hn,CutPatch.profile]


 

 


theorem adj_decompose_partners {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.Adj i j ↔ (p.omitTwo a b).Adj i j ∨
      (p.Occupied a ∧ ((i=a ∧ j=p.partnerOrSelf a) ∨ (j=a ∧ i=p.partnerOrSelf a))) ∨
      (p.Occupied b ∧ ((i=b ∧ j=p.partnerOrSelf b) ∨ (j=b ∧ i=p.partnerOrSelf b))) := by
  rw [adj_omit_decomposition]
  simp only [adj_partnerOrSelf]
  tauto

theorem omitTwo_swap_invariant {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    (p.omitTwo a b).Adj (Equiv.swap a b i) (Equiv.swap a b j) ↔
      (p.omitTwo a b).Adj i j := by
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp [Equiv.swap_apply_def,hia,hib,hja,hjb,omitTwo_adj]

theorem partnerOrSelf_ne {n : ℕ} (p : Pairing n) (a : Fin n) (ha : p.Occupied a) :
    p.partnerOrSelf a ≠ a := by
  intro he
  have hh := (adj_partnerOrSelf p a (p.partnerOrSelf a)).mpr ⟨ha,rfl⟩
  rw [he] at hh
  exact p.adj_irrefl a hh

theorem partnerOrSelf_ne_of_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (ha : p.Occupied a) (hb : ¬ p.Occupied b) : p.partnerOrSelf a ≠ b := by
  intro he
  have hh := (adj_partnerOrSelf p a (p.partnerOrSelf a)).mpr ⟨ha,rfl⟩
  rw [he] at hh
  exact hb ⟨a,adj_symm hh⟩

theorem swap_eq_partner_iff {n : ℕ} (p : Pairing n) (a b i : Fin n)
    (ha : p.Occupied a) (hb : ¬ p.Occupied b) :
    Equiv.swap a b i = p.partnerOrSelf a ↔ i = p.partnerOrSelf a := by
  have hx := p.partnerOrSelf_ne a ha
  have hy := p.partnerOrSelf_ne_of_vacant a b ha hb
  rw [← Equiv.eq_symm_apply]
  simp [Equiv.swap_apply_def,hx,hy]

theorem swap_eq_partner_iff_lower {n : ℕ} (p : Pairing n) (a b i : Fin n)
    (ha : ¬ p.Occupied a) (hb : p.Occupied b) :
    Equiv.swap a b i = p.partnerOrSelf b ↔ i = p.partnerOrSelf b := by
  rw [Equiv.swap_comm]
  exact swap_eq_partner_iff p b a i hb ha

 

def cutRelation {n : ℕ} (p : Pairing n) (a b : Fin n)
    (d : Finset (Fin 4 × Fin 4)) (i j : Fin n) : Prop :=
  (p.omitTwo a b).Adj i j ∨
    ∃ r s, CutPatch.boundaryAdj d r s ∧ p.cutLabels a b r = i ∧ p.cutLabels a b s = j

theorem cutRelation_empty {n : ℕ} (p : Pairing n) (a b i j : Fin n) :
    p.cutRelation a b ∅ i j ↔ (p.omitTwo a b).Adj i j := by
  simp [cutRelation,CutPatch.boundaryAdj]

theorem cutRelation_single {n : ℕ} (p : Pairing n) (a b i j : Fin n) (r s : Fin 4) :
    p.cutRelation a b {(r,s)} i j ↔ (p.omitTwo a b).Adj i j ∨
      (i=p.cutLabels a b r ∧ j=p.cutLabels a b s) ∨
      (i=p.cutLabels a b s ∧ j=p.cutLabels a b r) := by
  simp only [cutRelation,CutPatch.boundaryAdj,mem_singleton,Prod.mk.injEq]
  constructor
  · rintro (h|⟨x,y,(⟨rfl,rfl⟩|⟨rfl,rfl⟩),hi,hj⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hi.symm,hj.symm⟩)
    · exact Or.inr (Or.inr ⟨hi.symm,hj.symm⟩)
  · rintro (h|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r,s,Or.inl ⟨rfl,rfl⟩,rfl,rfl⟩
    · exact Or.inr ⟨s,r,Or.inr ⟨rfl,rfl⟩,rfl,rfl⟩

theorem cutRelation_union {n : ℕ} (p : Pairing n) (a b i j : Fin n)
    (d e : Finset (Fin 4 × Fin 4)) :
    p.cutRelation a b (d ∪ e) i j ↔
      p.cutRelation a b d i j ∨ p.cutRelation a b e i j := by
  simp only [cutRelation,CutPatch.boundaryAdj,mem_union]
  constructor
  · rintro (h|⟨x,y,h,hi,hj⟩)
    · exact Or.inl (Or.inl h)
    · rcases h with (h|h) | (h|h)
      · exact Or.inl (Or.inr ⟨x,y,Or.inl h,hi,hj⟩)
      · exact Or.inr (Or.inr ⟨x,y,Or.inl h,hi,hj⟩)
      · exact Or.inl (Or.inr ⟨x,y,Or.inr h,hi,hj⟩)
      · exact Or.inr (Or.inr ⟨x,y,Or.inr h,hi,hj⟩)
  · rintro ((h|⟨x,y,h,hi,hj⟩)|(h|⟨x,y,h,hi,hj⟩))
    · exact Or.inl h
    · exact Or.inr ⟨x,y,h.imp Or.inl Or.inl,hi,hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨x,y,h.imp Or.inr Or.inr,hi,hj⟩

end Pairing
end
end CriticalStrip.Diagram

end OAI
