import OAI.Geometry.Convex.GeneralMahler.Scalar.Pass
import OAI.Geometry.Convex.GeneralMahler.Intervals.Trig

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag CJet Jet Profile Cert Cert.IV

structure Line where
  x:Int
  k:Int
  c:Int
  q:Int
  u:Int
  v:Int
  mx:Int
deriving Repr, Inhabited

def dn8:Int:=den/100000000
def GB (a:Int):IV:=box ((a-3)*dn8) ((a+3)*dn8) -- ±3e-8
def GP (a:Int):IV:=box (a*dn8) (a*dn8)
noncomputable def gv (a:Int):ℝ:=a/100000000
lemma mGP (a:Int): gv a∈ GP a := by
  change IV.w _≤_ ∧ _≤ IV.w _
  rw [show IV.w (a*dn8)=gv a from by unfold gv IV.w; norm_num [dn8,den]; ring]
  exact ⟨le_rfl,le_rfl⟩

def inData (n:Nat) (L:Line): Bool:=
  let A := pG n
  let cv:=trbox 8 (bd 46000*nbox n)
  SubB A.X (GB L.x) &&
    SubB (A.Kj 0) (GB L.k) && SubB (A.Cj 0) (GB L.c) &&
    SubB (A.Qj 0) (GB L.q) && SubB (bd 2200*cv.1) (GB L.u) &&
    SubB (bd 2200*cv.2) (GB L.v)
def checkL (n:Nat) (L:Line):Bool:=
  inData n L && (if n<720 then pass n && LeB (tot n K) (GP L.mx) else true)

structure NodeTrue (n:ℕ) (L:Line) : Prop where
  xx: xs (nd n)∈ GB L.x
  k : K.act (nd n)∈ GB L.k
  c : C.act (nd n)∈ GB L.c
  q : Q.act (nd n)∈ GB L.q
  u : uc (xs (nd n)) ∈ GB L.u
  v : us (xs (nd n)) ∈ GB L.v
lemma nodeC (n:ℕ) (L:Line) (h:inData n L=true): NodeTrue n L := by
  let p:=pGa n
  have hk:=p.mK 0; have hc:=p.mC 0; have hq:=p.mQJ 0
  have hm: omegaP∈ bd 46000 := by convert mbd 46000; norm_num [omegaP]
  have hr: Profile.r∈ bd 2200 := by convert mbd 2200; norm_num [r]
  obtain ⟨ha,hb⟩:= mtrbox (mmul hm (mgrid n)) 8
  simp only [inData,Bool.and_eq_true] at h
  rw [k0s,k_stable] at hk;rw [c0s,c_stable] at hc;rw [qje] at hq
  refine ⟨subB p.X h.1.1.1.1.1,subB hk h.1.1.1.1.2,subB hc h.1.1.1.2,subB hq h.1.1.2,?_,?_⟩
  · unfold uc; rw [x_ang]; exact subB (mmul hr ha) h.1.2
  unfold us; rw [x_ang]; exact subB (mmul hr hb) h.2

lemma line_good (n:ℕ) (L:Line) (h:checkL n L=true) :
    NodeTrue n L∧(n<720 → pass n=true ∧ ∀ x∈Icc (nd n) (nd (n+1)), K.act x ≤ gv L.mx) := by
  simp only [checkL,Bool.and_eq_true] at h
  refine ⟨nodeC n L h.1,fun hn=>?_⟩
  have hh:=h.2; rw [ite_eq_left hn] at hh; simp only [Bool.and_eq_true] at hh
  refine ⟨hh.1,fun x hx=>?_⟩
  have hp:=htot n K IK x hx
  have he : K.Fld x 0=K.act x:=FldK x
  rw [he] at hp
  exact mle hp (mGP _) hh.2

-- The check recurses on the number of grid cells.
def runB (p:ℕ→Bool) (n:ℕ):ℕ→Bool
  | 0=>true
  | r+1=> p (n+r)&&runB p n r
def By (f:ℕ→Bool) (l u:Nat): Prop:=∀ i,l ≤ i → i < u → f i=true
lemma byRun (p:ℕ→Bool) (n m k:ℕ) (he:n+m=k) (h:runB p n m=true): By p n k := by
  subst k
  induction m with
  | zero=> intro i h1 h2; omega
  | succ m ih=>
    simp only [runB,Bool.and_eq_true] at h
    intro i h1 h2; by_cases H:i=n+m
    · exact H.symm ▸ h.1
    apply ih h.2 _ h1; omega
lemma byJoin {p:ℕ→Bool} {x y z:ℕ} (h:By p x y) (hh:By p y z):
    By p x z := by intro i he hz; rcases lt_or_ge i y with h'|h'; exact h i he h'; exact hh i h' hz
end GeneralMahler.SCal.Grid

end OAI
