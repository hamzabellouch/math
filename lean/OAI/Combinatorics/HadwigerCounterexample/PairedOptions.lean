import OAI.Combinatorics.HadwigerCounterexample.FiniteTableEnumeration
import OAI.Combinatorics.HadwigerCounterexample.InitialPartitionExistence
import OAI.Combinatorics.HadwigerCounterexample.HistogramBounds
import OAI.Combinatorics.HadwigerCounterexample.KeyTestCorrespondence

namespace OAI

/-! # Paired Options -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Submodule Function
open scoped BigOperators
namespace StatusAnalysis
variable {p : Shape} {n N K : ℕ}

structure Quill (p : Shape) (q : Format) (d : Rates) (b : Bool) where
  sel : Messenger q → Label p.b
  flav : Messenger q → Flavor p.g
  amp : Amounts p q d b
  script : Script p (Messenger q)

structure Typus (p : Shape) (q : Format) (d e : Rates) where
  t : Tagging p (Messenger q)
  z : Messenger q → F
  qA : Quill p q d true
  qB : Quill p q e false

abbrev Volumes := Grid → Fin 8
abbrev Stakes (K : ℕ) := Nodes → Fin (K^2+1)
abbrev Master (K : ℕ) := Volumes × Stakes K × Stakes K
def toFormat (q : Volumes) : Format := fun i=>(q i).val
def toRates {K : ℕ} (d : Stakes K) : Rates := fun i=>(d i).val
abbrev OnFile (p : Shape) {K : ℕ} (q : Master K) :=
  Typus p (toFormat q.1) (toRates q.2.1) (toRates q.2.2)
abbrev Scrip (p : Shape) (K : ℕ) := Σ q : Master K, Fin (2^deckMax p K) × OnFile p q

instance quillFintype (p : Shape) (q : Format) (d : Rates) (b : Bool) :
    Fintype (Quill p q d b) := by
  classical
  let A := (Messenger q → Label p.b) × (Messenger q→Flavor p.g) × Amounts p q d b × Script p (Messenger q)
  let E : A≃Quill p q d b := {
    toFun x:= ⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:= (x.sel,x.flav,x.amp,x.script)
    left_inv _ := rfl
    right_inv _:=rfl }
  letI : Fintype (Messenger q → Flavor p.g):= by infer_instance
  letI : Fintype (Amounts p q d b) := by infer_instance
  letI : Fintype (MOne p):= by unfold MOne MIdx; infer_instance
  letI : Fintype (Vec (MOne p)):= by infer_instance
  letI : Fintype (Messenger q →Vec (MOne p)):= by infer_instance
  letI : Fintype (Script p (Messenger q)):= by infer_instance
  exact Fintype.ofEquiv _ E
instance typusFintype (p : Shape) (q : Format) (d e : Rates) : Fintype (Typus p q d e) := by
  classical
  let A:=Tagging p (Messenger q)× (Messenger q→F) ×Quill p q d true×Quill p q e false
  let E : A≃Typus p q d e := {
    toFun x:=⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:=(x.t,x.z,x.qA,x.qB)
    left_inv _:=rfl
    right_inv _:=rfl }
  exact Fintype.ofEquiv _ E
instance scripFintype (p : Shape) (K : ℕ) : Fintype (Scrip p K) := by
  classical
  infer_instance

variable {q : Format} {d e : Rates}

namespace Quill
variable {b : Bool} (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q→F)

def pen := manager b t w.sel w.flav
def moral :=
    Injective w.sel ∧ owing p b w.amp z ∧ ∀ i, (w.amp i).1.feasible (t i) (w.flav i)

theorem canDraw {w : Quill p q d b} (h : w.moral t z) (i : Messenger q) :
    canDial p (t i) (w.flav i) (z i) :=
  ⟨_,h.2.2 i,h.2.1 i⟩

def penSpace (x : Pin p n N) (K : ℕ) :=
   ∀ y:Inputs p n (Messenger q), ((w.pen t).draw y).avoids x.sp (qorth K)

def signed (x y : Pin p n N) (s : Charts p n d) (T : Cross p n) (K : ℕ) :=
    charted s x.sp ∧ w.penSpace t x K ∧ still b w.amp s T ∧ tableInj x.sp y.sp T

def deposit (m : Mixer p n) (o : UnitType p n N) (v : Charts p n d)
    (x : Inputs p n (Messenger q)) :=
  let u := (w.pen t).draw x
  printed b v t w.sel w.flav m o x=w.amp ∧
    u.reads w.script m ∧ ownPart t z (u.keys t o)

def sales (μ : Wgt (UnitType p n N)) (P : UnitType p n N→Prop)
    (m :Mixer p n) (s : Charts p n d) : Wgt (Keys (p:=p) t N) :=
  Volley.hist (w.pen t).draw t μ ((w.pen t).state z n)
    (fun x o=> P o∧w.deposit t z m o s x)

end Quill

namespace Typus
variable (w : Typus p q d e)
def permission :=
  (∀ i,1 ≤ q i∧q i≤7) ∧
  w.qA.moral w.t w.z ∧ w.qB.moral w.t w.z ∧
  (∀ i,fullq w.z i=1) ∧ rhyme w.qA.amp w.qB.amp ∧
  proclaims p w.qA.amp w.qB.amp w.t w.qA.script ∧
    proclaims p w.qB.amp w.qA.amp w.t w.qB.script

def chances (s : Charts p n d) (v : Charts p n e)
    (x y : Pin p n N) (T : Cross p n) (K : ℕ) :=
  w.permission ∧ w.qA.signed w.t x y s T K ∧ w.qB.signed w.t y x v (reciprocal p T) K
end Typus

def notified (m : Mixer p n) (x y : Pin p n N) (T : Cross p n)
    (C : Prop) (o : UnitType p n N) :=
  C ∧ x.agree o ∧ (∀ i,frameLaw m (onSide o i)) ∧ tableFlag x y T o

structure Station (p : Shape) (n N K : ℕ) (s : LeafMixture p n N) where
  cAxes : s.T → (d:Rates)→Charts p n d
  mails : s.T → s.T → Fin (2^deckMax p K) → Cross p n
namespace Station
variable {s : LeafMixture p n N} (v : Station p n N K s)

def bank :=
  (∀ i,dressCode (p:=p) n (s.pin i.val).sp (v.cAxes i)) ∧
  ∀ i j T,∃ k,fitsTable (s.pin i.val).sp (s.pin j.val).sp (v.mails i j k) T
where
  dressCode {p : Shape} (n : ℕ) (f : Plan p n) (V : (d:Rates)→ Charts p n d) :=
    let d:=fun i=>dim (effective f i)
    charted (V d) f

theorem create (h : ∀ i:s.T, planRank (s.pin i.val).sp ≤K) :
    ∃ v : Station p n N K s,v.bank := by
  classical
  let d (i:s.T) j:=dim (effective (s.pin (Subtype.val i)).sp j)
  choose F hF using fun i:s.T=> chart_create p n (s.pin i.val).sp
  choose G hG using fun i j:s.T=> deck_cast p n K (s.pin i.val).sp (s.pin j.val).sp (h i) (h j)
  let axes (i:s.T) (r:Rates): Charts p n r := if ht:r=d i then ht ▸ (F i) else fun _=>0
  refine ⟨⟨axes,G⟩,fun i=>?_,hG⟩
  change charted (axes i (d i)) _
  unfold axes; rw [dite_eq_left rfl]; exact hF i

variable (w : Typus p q d e)

def news (i j : s.T) (k : Fin (2^deckMax p K)) :=
  w.chances (v.cAxes i d) (v.cAxes j e) (s.pin i.val) (s.pin j.val) (v.mails i j k) K
def frontPage (m : Mixer p n) (i j : s.T) (k : Fin (2^deckMax p K)) :=
  notified m (s.pin i.val) (s.pin j.val) (v.mails i j k) (news v w i j k)
def backPage (m : Mixer p n) (i j : s.T) (k : Fin (2^deckMax p K)) :=
  notified m (s.pin j.val) (s.pin i.val) (reciprocal p (v.mails i j k)) (news v w i j k)

def leftSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T)
    (k : Fin (2^deckMax p K)) :=
  w.qA.sales w.t w.z (partW μ i.val) (frontPage v w m i j k) m (v.cAxes i d)
def rightSales (m : Mixer p n) (μ : Wgt (UnitType p n N)) (i j : s.T)
    (k : Fin (2^deckMax p K)) :=
  w.qB.sales w.t w.z (partW μ j.val) (backPage v w m i j k) m (v.cAxes j e)

def matchScore (m:Mixer p n) (μ: Wgt (UnitType p n N)) (i j:s.T)
    (k : Fin (2^deckMax p K)) :=
  overlap (lawNu p N w.t w.z) (leftSales v w m μ i j k) (rightSales v w m μ i j k)

def arena (m:Mixer p n) (μ: Wgt (UnitType p n N)) (k:Fin (2^deckMax p K)) :=
  avg (pairW (portionW μ s.T) (portionW μ s.T)) (fun x=>matchScore v w m μ x.1 x.2 k)
end Station
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
