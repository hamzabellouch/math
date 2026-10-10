import OAI.Combinatorics.HadwigerCounterexample.LeafMixtures
import OAI.Combinatorics.HadwigerCounterexample.CoverAlternatives
import OAI.Combinatorics.HadwigerCounterexample.ZeroDiscrepancyLemma

namespace OAI

/-! # Preparation Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

structure PreparationParameters where
  D : ℕ
  L : ℝ
  d : ℕ
  e : ℕ
  s : ℕ
  u : ℕ
  k : ℕ
  ζ : ℝ
  B : ℕ

namespace PreparationParameters
def pins (q : PreparationParameters) := 3*q.e+q.s
def rank (q : PreparationParameters) := 2*q.e + 2

def leafOld (q : PreparationParameters) : ℝ := ↑q.D+q.e+2
def leafNew (q : PreparationParameters) : ℝ := q.leafOld+q.u+q.s+2
def spJoint (q : PreparationParameters) : ℝ := (q.D:ℝ)+1

def spear (q : PreparationParameters) := bp (100)*q.L

structure allows (q : PreparationParameters) : Prop where
  pos : 0< q.ζ
  small : q.ζ < 1
  hL : 0≤q.L
  bigS : q.leafOld+q.u+q.ζ ≤ (q.ζ-q.ζ/4) * q.s

variable {p : Shape} {M n N : ℕ}
abbrev tale (p : Shape) (M : ℕ) := ∀ n,Wgt (UnitType p n (M*n))
abbrev rhythms (p : Shape) (M : ℕ) := ∀ n,LeafMixture p n (M*n)
abbrev cycleM (p : Shape) := ∀ n,Mixer p n

def frameSide (p : Shape) (m : Mixer p n) (x : UnitType p n N) :=
  ∀ i,frameLaw m (onSide x i)
def usual (p : Shape) (m : Mixer p n) (N : ℕ) :=
  pairW (raw m N) (raw m N)

structure nascent (q : PreparationParameters) (p : Shape) (N : ℕ) {n}
    (w : Wgt (UnitType p n N)) (m : Mixer p n) : Prop where
  law : IsLaw w
  border : bySide p w m q.L
  total : ∀ x,w x≤bp ((q.D:ℝ)*N)*usual p m N x

structure entered (q : PreparationParameters) (p : Shape) (N : ℕ) {n} (m : Mixer p n)
    (w : Wgt (UnitType p n N)) (s : LeafMixture p n N) : Prop where
  weight : (1/2:ℝ) ≤ s.amount w
  strength : s.strength w (usual p m N) q.leafOld q.ζ q.e
  onTile : s.within (fun x=>w x≠0 ∧ (rawHoles m).unit x ∧ joins x≤2*q.D ∧ frameSide p m x)

structure durable (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) : Prop where
  mass : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>(s i).amount (w i))
  shape : ∀ᶠ n in l,(s n).strength (w n) (usual p (m n) (M*n)) q.leafNew (2*q.ζ) q.pins ∧
    (s n).within (frameSide p (m n))

def seems (q : PreparationParameters) (p : Shape) (m : Mixer p n)
    (s : LeafMixture p n N)
    (x : UnitType p n N) (g : Bool → Augur p N) (z : Bool → Profile p n)
    (L : Bool→Finset (Label p.b)) (α : Party) (ε : ℝ) :=
  (∀ i : Bool,(L i).card≤ q.B ∧ z i∈ effective (s.rooting x) i) ∧
    claimed p x g m z α L ε

def predicts (q : PreparationParameters) (p : Shape) (N : ℕ) {n} (m : Mixer p n)
    (s : LeafMixture p n N) (w : Wgt (UnitType p n N)) (ε : ℝ) :=
  ∃ g : Bool → Augur p N, (0.000001 : ℝ) ≤ pr (s.sap w) (fun x => ∃ z L α, q.seems p m s x g z L α ε)

def silenceOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) :=
  ∃ ε:ℝ,0<ε∧∀ᶠ n in l, ¬q.predicts p (M*n) (m n) (s n) (w n) ε ∧
    let v:=(s n).sap (w n)
    0.99 < pr (pairW v v) (secureAt p (s n).rooting)

structure Sketch (p : Shape) (M : ℕ) where
  c : PredictionClass
  α : Party
  r : F
  m : ∀ n,BMark p n (M*n)
  L : ∀ n,UnitType p n (M*n) → Bool → Finset (Label p.b)
  g : Bool → PredictionClass.season p M
  ε : ℕ→ℝ

def engrave (b : Sketch p M) (q : PreparationParameters) (m : cycleM p) (s : rhythms p M) (n : ℕ) :=
  fun x : UnitType p n (M*n) =>
  q.seems p (m n) (s n) x (fun i=> b.g i n) (b.m n x) (b.L n x) b.α (b.ε n) ∧
    glint p (b.m n x) = b.r ∧ (b.c=dusk → exactInk p (m n) (b.m n) x)

structure ledger (b : Sketch p M) (l : Filter ℕ) : Prop where
  small : slight l b.ε
  classes : ∃ τ:ℝ, 0<τ∧∀ᶠ n in l,b.c.recital p (fun i=>b.g i n) b.α τ
  light : b.c.lit b.α

structure bright (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (s : rhythms p M) (b : Sketch p M) : Prop where
  forecasts : ledger b l
  engraved : ∀ᶠ n in l,(s n).within (engrave b q m s n)

def matchProg (b : Sketch p M) (n : ℕ) :=
  matchUp (delta (b.m n)) b.α b.r b.c
def glow (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n))) (matchProg b n)
def gleam (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
     (fun x=>matchProg b n x∧¬secureAt p (s n).rooting x)
def gilded (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ) :=
  pr (pairW ((s n).sap (w n)) ((s n).sap (w n)))
     (fun x=>matchProg b n x∧secureAt p (s n).rooting x)

theorem gilding (s : rhythms p M) (w : tale p M) (b : Sketch p M) (n : ℕ)
    (h : IsLaw ((s n).sap (w n))) :
    glow s w b n-gleam s w b n≤gilded s w b n := by
  let G:= matchProg b n
  let Q := secureAt p (s n).rooting
  have ht (x) : G x → (G x∧ Q x) ∨ (G x ∧¬Q x) := by tauto
  have hv := pairW_law h h
  have hx : glow s w b n ≤ gilded s w b n+gleam s w b n :=
    (pr_mono hv.nz ht).trans (pr_or_le hv.nz)
  linarith only [hx]

def glowOutcome (l : Filter ℕ) (p : Shape) (M : ℕ)
    (w : tale p M) (s : rhythms p M) (b : Sketch p M) :=
  ∃ e:ℝ,0<e∧∀ᶠ n in l,e ≤ gilded s w b n

def hardened (q : PreparationParameters) (p : Shape) (N : ℕ) {n}
    (s : LeafMixture p n N) (z : BMark p n N) :=
  ∃ T : Cov p N, cdim p T ≤ q.d ∧ (s.within (fun x=> covered p T (delta z x))) ∧
    ∀ i∈s.T,∃ a,specialLeaf T z a i (s.pin i) ∧
      ∀ x∈i,∀ j,z x j ∈ effective a.sp j

def glimmer (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (w : tale p M) (s : rhythms p M) (b : Sketch p M) :=
  b.c=dusk ∧ ∃ e:ℝ,0<e∧∀ᶠ n in l,q.hardened p (M*n) (s n) (b.m n) ∧
    e/((M*n:ℕ):ℝ)^4 ≤ glow s w b n ∧ gleam s w b n≤0.001*glow s w b n

def predOutcome (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ) (m : cycleM p)
    (w : tale p M) (s : rhythms p M) :=
    ∃ b : Sketch p M,q.bright l p M m s b ∧ (glowOutcome l p M w s b ∨ q.glimmer l p M w s b)

def intern (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
  ∀ m : Mixer p n,PhaseReady p n N (mstep q.rank) (N/denomStep q.rank) q.rank q.k q.d m
     (tinyPhase p.g q.rank q.spJoint) coin warn (heatloss q.rank q.k) q.spear
     (bp (q.spJoint*N))

def outside (q : PreparationParameters) (p : Shape) (n N : ℕ) :=
   ∀ P:UnitType p n N×UnitType p n N→Prop, named P (bp (3*q.d*(N:ℝ))) →
    named (P ∘ Prod.swap) (bp (3*q.d*(N:ℝ))) →
    ∀ w (b:Fpins p n N) (m:Mixer p n),(∀ x,planRank (b x)≤q.pins) →
    IsLaw w → bySide p w m (shine N) → (∀ x,w x≠0 → ∀ i,frameLaw m (onSide x i)) →
    pr (pairW w w) (fun x=>P x ∧ ¬secureAt p b x) ≤ 0.0005*pr (pairW w w) P+edgeError N
structure planted (q : PreparationParameters) (p : Shape) (M : ℕ) : Prop where
  early : q.allows
  hM : 1≤M
  hg : Odd p.g
  hG : 3≤p.g
  hJ : 1≤p.j
  hR : 1≤p.r
  hB : (q.B:ℝ)<bp ((p.b:ℝ)-2*p.j)
  hD : 8*q.D<p.g*p.g
  room : ∃ d_:ℕ,4*q.D≤p.g*d_∧2*screenRank p q.e+1 ≤ ((p.g-1)/2)*(p.g-d_)*p.r
  wrap : ∀ᶠ n : ℕ in atTop, let N:=M*n;
    2*num (Full p n)<N ∧ (3*q.d+2*q.e:ℝ)*N+2*q.e^2≤ ((q.u:ℝ)-1)*N ∧
    (∀ (m : Mixer p n) (a : Pin p n N), pr (usual p m N) a.agree ≤ fee N (q.ζ/4) (planRank a.sp)) ∧
      q.intern p n N ∧ q.outside p n N

end PreparationParameters
end HadwigerCounterexample

end

end OAI
