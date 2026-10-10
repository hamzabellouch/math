import OAI.Combinatorics.HadwigerCounterexample.IndependentColumnBatches
import OAI.Combinatorics.HadwigerCounterexample.CollisionInequality

namespace OAI

/-! # Bounded Query Templates -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Module LinearMap Function
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

structure Template (p : Shape) (I : Type) where
  aim : I→Bool
  t : Tagging p I
  s : I→Label p.b
  f : I→Flavor p.g

abbrev Inputs (p : Shape) (n : ℕ) (I : Type) := I → Knobs p.g n

namespace Template
variable (v : Template p I)

def draw (y : Inputs p n I) : Volley p n I where
  obj := v.aim
  sel := v.s
  par i := lit (v.f i) (v.t i) (y i)

def state (q : I→F) (n : ℕ) : Wgt (Inputs p n I) :=
  prodW (fun i : I => scopedBit p n (v.t i) (v.f i) (q i))
omit [Fintype I] [DecidableEq I] in
theorem draw_legal (y : Inputs p n I) : (v.draw y).legal v.t :=
  fun _ => lit_allows _ _ _
end Template

abbrev KeySlots (p : Shape) (t : Tagging p I) := Σ i, TagStar (t i)

def scatter (t : Tagging p I) (N : ℕ) : Keys (p:=p) t N ≃ Rack (KeySlots p t) N where
  toFun x := (Matrix.of (fun j i => x i.1 i.2 true j),Matrix.of (fun j i => x i.1 i.2 false j))
  invFun x := fun i j b => if b then x.1.col ⟨i,j⟩ else x.2.col ⟨i,j⟩
  left_inv x := by funext i j b; cases b <;> rfl
  right_inv x := by apply Prod.ext <;> rfl

def globPort (p : Shape) (t : Tagging p I) (q : I→Bool) :
    Route (KeySlots p t) (Ports p) :=
  fun x => (q x.1,x.2.val)

def nomAsk (t : Tagging p I) (v : Volley p n I) :
    NomQuery p n (globPort p t v.obj) :=
  fun _ => Matrix.of (fun i j => v.rayAt j.val.1 i)

omit [Fintype I] [DecidableEq I] in
theorem peek_keys (t : Tagging p I) (v : Volley p n I) (x : UnitType p n N) :
    peekR p (globPort p t v.obj) (nomAsk t v) (nomAsk t v) (mergeR p x) =
      scatter t N (v.keys t x) := by
  apply Prod.ext
  · ext i j; rfl
  · ext i j; rfl

theorem raw_keys (t : Tagging p I) (v : Volley p n I) (m : Mixer p n) {N : ℕ}
    (hN : 2*num (Full p n)<N) (ha : ∀ i, Injective (nomAsk t v i).mulVec) :
    let r := raw m N
    mapW (pairW r r) ((scatter t N) ∘ v.keys t) = rackStation (database m (nomAsk t v) (nomAsk t v)) N := by
  classical
  let g := globPort p t v.obj
  let A := nomAsk t v
  have hh := law_peekR m hN ha ha
  rw [← law_mergeR m N, mapW_nested] at hh
  refine Eq.trans ?_ hh
  congr 1

def ownPort (t : Tagging p I) : Route (KeySlots p t) (Comp p.g) := fun x => x.2.val
def ownMap (t : Tagging p I) (q : I→F) : GeoM (ownPort (p:=p) t) :=
  fun _ => Matrix.diagonal (fun i => q i.val.1)
def ownPart (t : Tagging p I) (q : I→F) {N : ℕ}
    (x : Keys (p:=p) t N) :=
  gramPart (ownMap (p:=p) t q) (scatter t N x)
def lawNu (p : Shape) (N : ℕ) (t : Tagging p I) (q : I→F) :
    Wgt (Keys (p:=p) t N) := unifOn (ownPart (p:=p) t q)

theorem lawNu_rack (t : Tagging p I) (q : I→F) :
    mapW (lawNu p N t q) (scatter t N) = rackWave (ownMap t q) N :=
  on_equiv ..

def ownOne (p : Shape) {N : ℕ} (l : Tag p.g) (q : F) (x : AtomKey (p:=p) l N) :=
  ∀ i,dotProduct (x i true) (x i false) = q
def lawOmega (p : Shape) (N : ℕ) (l : Tag p.g) (q : F) :
    Wgt (AtomKey (p:=p) l N) := unifOn (ownOne p l q)

omit [Fintype I] in
theorem ownPart_def (t : Tagging p I) (q : I→F) {N : ℕ} (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x ↔
    (∀ i, ownOne p (t i) (q i) (x i)) ∧
      ∀ (i j : I) (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)), i≠j →
        dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false)=0 := by
  classical
  let Q := ownPort (p:=p) t
  unfold ownPart
  rw [part_scores]
  have he i j (e : Comp p.g) (hi : inc e (t i)) (hj : inc e (t j)) :
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
      scoreR (scatter t N x) a b=dotProduct (x i ⟨e,hi⟩ true) (x j ⟨e,hj⟩ false) := rfl
  constructor
  · intro h
    constructor
    · rintro i ⟨e,hi⟩
      let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
      exact (he i i e hi hi).symm.trans ((h e a a).trans (Matrix.diagonal_apply_eq ..))
    intro i j e hi hj heq
    let a : Port Q e := ⟨⟨i,⟨e,hi⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hj⟩⟩,rfl⟩
    have hh : a≠b := fun h => heq (congrArg (fun x:Port Q e => x.val.1) h)
    exact (he i j e hi hj).symm.trans ((h e a b).trans (Matrix.diagonal_apply_ne _ hh))
  · rintro ⟨h,h'⟩ e ⟨⟨i,v⟩,ha⟩ ⟨⟨j,w⟩,hb⟩
    rcases v with ⟨v,hv⟩; rcases w with ⟨w,hw⟩
    change v = e at ha; change w=e at hb
    subst v; subst w
    let a : Port Q e := ⟨⟨i,⟨e,hv⟩⟩,rfl⟩
    let b : Port Q e := ⟨⟨j,⟨e,hw⟩⟩,rfl⟩
    by_cases he : i=j
    · subst j
      refine (show scoreR (scatter t N x) a.val a.val=_ from h i ⟨e,hv⟩).trans ?_
      exact (Matrix.diagonal_apply_eq (fun j : Port Q e => q j.val.1) a).symm
    have hh : a≠b := fun h => he (congrArg (fun x:Port Q e => x.val.1) h)
    refine Eq.trans (h' i j e hv hw he) ?_
    exact (Matrix.diagonal_apply_ne (fun j : Port Q e => q j.val.1) hh).symm

end HadwigerCounterexample

end

end OAI
