import OAI.Combinatorics.HadwigerCounterexample.BoundedQueryTemplates
import OAI.Combinatorics.HadwigerCounterexample.GramConditionedLaws

namespace OAI

/-! # Key Reference Laws -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I] {p : Shape} {n N : ℕ}

abbrev Toast (p : Shape) := Fin (p.g-1)
def outlet (p : Shape) (l : Tag p.g) : Toast p ≃ TagStar l :=
  (Fintype.equivFinOfCardEq (card_star l)).symm
def channelTag (p : Shape) (l : Tag p.g) (i : Toast p) := (outlet p l i).val
theorem channelTag_inj (p : Shape) (l : Tag p.g) : Injective (channelTag p l) :=
  Subtype.val_injective.comp (outlet p l).injective

def mug (p : Shape) (l : Tag p.g) (N : ℕ) : AtomKey (p:=p) l N ≃ Rack (Toast p) N where
  toFun x := (Matrix.of (fun i j => x (outlet p l j) true i),Matrix.of (fun i j =>
    x (outlet p l j) false i))
  invFun x := fun i b j => if b then x.1 j ((outlet p l).symm i) else x.2 j ((outlet p l).symm i)
  left_inv x := by
    funext i b j
    cases b <;> simp
  right_inv x := by apply Prod.ext <;> ext <;> simp

def tray (p : Shape) (t : Tagging p I) (N : ℕ) : Keys (p:=p) t N ≃ Rack (I×Toast p) N :=
  (Equiv.piCongrRight (fun i => mug p (t i) N)).trans (relay I (Toast p) N).symm

def handles (p : Shape) (t : Tagging p I) : I×Toast p ≃ KeySlots p t where
  toFun x := ⟨x.1,outlet p (t x.1) x.2⟩
  invFun x := (x.1,(outlet p (t x.1)).symm x.2)
  left_inv x := by simp
  right_inv x := by simp
def trayPort (p : Shape) (t : Tagging p I) : Route (I×Toast p) (Comp p.g) :=
  fun x => channelTag p (t x.1) x.2
def trayJoin (p : Shape) (t : Tagging p I) (e : Comp p.g) :
    Port (trayPort p t) e ≃ Port (ownPort (p:=p) t) e where
  toFun x := ⟨handles p t x.val,x.property⟩
  invFun x :=
    ⟨(handles p t).symm x.val,by
      have h : (ownPort t) ∘ (handles p t)=trayPort p t := rfl
      rw [←h]; simp only [Function.comp_apply,Equiv.apply_symm_apply]; exact x.property⟩
  left_inv x := Subtype.ext (Equiv.symm_apply_apply ..)
  right_inv x := Subtype.ext (Equiv.apply_symm_apply ..)

def trayMap (p : Shape) (t : Tagging p I) (q : I → F) : GeoM (trayPort p t) :=
  fun e => (ownMap (p:=p) t q e).submatrix (trayJoin p t e) (trayJoin p t e)

omit [DecidableEq I] in
theorem tray_sips (p : Shape) (t : Tagging p I) (N : ℕ) (x : Keys (p:=p) t N) (i : I) :
    led i (tray p t N x)=mug p (t i) N (x i) := by apply Prod.ext <;> rfl

theorem tray_wave (p : Shape) (t : Tagging p I) (q : I→ F) (x : Keys (p:=p) t N) :
    ownPart (p:=p) t q x↔ gramPart (trayMap p t q) (tray p t N x) := by
  classical
  unfold ownPart
  rw [part_scores,part_scores]
  let y := scatter t N x
  let z := tray p t N x
  let A := trayMap p t q
  let g := handles p t
  have hi i j : scoreR z i j=scoreR y (g i) (g j) := rfl
  constructor
  · exact fun h i a b => h i (trayJoin p t i a) (trayJoin p t i b)
  intro hh i a b
  obtain ⟨a,rfl⟩ := (trayJoin p t i).surjective a
  obtain ⟨b,rfl⟩ := (trayJoin p t i).surjective b
  exact hh i a b
theorem lawtray (p : Shape) (t : Tagging p I) (q : I → F) :
    mapW (lawNu p N t q) (tray p t N) = rackWave (trayMap p t q) N := by
  unfold lawNu
  have h : ownPart (p:=p) t q (N:=N)=(fun x => gramPart (trayMap p t q) (tray p t N x)) :=
    funext fun i => propext (tray_wave ..)
  rw [h]
  exact on_equiv ..

omit [Fintype I] in
theorem mug_wave (p : Shape) (t : Tagging p I) (q : I→F) (i : I)
    (x : AtomKey (p:=p) (t i) N) :
    ownOne p (t i) (q i) x ↔ gramPart (laneM (trayMap p t q) i) (mug p (t i) N x) := by
  classical
  rw [part_scores]
  let g := trayPort p t; let b := street g i
  let X := mug p (t i) N x
  let A := laneM (trayMap p t q) i
  have hi {j} (a : Port b j) :
      scoreR X a.val a.val=dotProduct (x (outlet p (t i) a.val) true)
        (x (outlet p (t i) a.val) false) := rfl
  have hj {j} (a : Port b j) : A j a a=q i := by
    let s := trayJoin p t j (condLane (trayPort p t) i j a)
    exact Matrix.diagonal_apply_eq (fun i : Port (ownPort (p:=p) t) j => q i.val.1) s
  have hh (a c : Toast p) (h : b a=b c) : a=c := channelTag_inj p (t i) h
  constructor
  · intro he j a c
    have h : c=a := Subtype.ext (hh _ _ (c.property.trans a.property.symm)); subst c
    exact (hi a).trans ((he _).trans (hj a).symm)
  intro h j
  obtain ⟨a,rfl⟩ := (outlet p (t i)).surjective j
  let e := b a
  let c : Port b e := ⟨a,rfl⟩
  exact (hi c).symm.trans ((h e c c).trans (hj c))

omit [Fintype I] in
theorem lawmug (p : Shape) (t : Tagging p I) (q : I → F) (i : I) :
    mapW (lawOmega p N (t i) (q i)) (mug p (t i) N) = rackWave (laneM (trayMap p t q) i) N := by
  unfold lawOmega
  rw [show ownOne p (t i) (q i) (N:=N)=
    (fun x => gramPart (laneM (trayMap p t q) i) (mug p (t i) N x)) from
    funext fun x => propext (mug_wave ..)]
  exact on_equiv ..
end HadwigerCounterexample

end

end OAI
