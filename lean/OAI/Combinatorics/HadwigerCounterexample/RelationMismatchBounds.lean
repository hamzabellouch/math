import OAI.Combinatorics.HadwigerCounterexample.FiniteDualSystems

namespace OAI

/-! # Relation Mismatch Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function Submodule LinearMap
open scoped BigOperators Topology
open Template
variable {p:Shape} {N n r K : ℕ}
namespace StatusAnalysis
namespace DualAnalysis
open Club Guild
variable {d e : Rates}
    {u:Terrain p r} {s:Gazette p r d} {t:Gazette p r e}
    {β η δ:ℝ}

def seeking (p : Shape) (A : Stalls p) :=
  ∀ i, (A i).card+902 < Fintype.card (Label p.b)
theorem any_label (A : Finset (Label p.b)) (h : A.card<Fintype.card (Label p.b)) :
    ∃ x,x∉A := by
  by_contra! hh
  have hf := card_le_card (show univ ⊆ A from fun _ _=>hh _)
  rw [card_univ] at hf; exact h.not_ge hf

theorem generic_apt (p:Shape) (hg:3≤p.g) (x:Appearance p) (hx:x.f=Flavor.full) :
    x.apt := by obtain ⟨s,h1,h2,h3⟩:=generic_summary p hg x.l x.q 0; exact ⟨s,hx ▸ h1,h2⟩

set_option maxHeartbeats 900000 in
theorem plenitude (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (hg:3 ≤ p.g) (A B:Stalls p) (hk:seeking p A) (hl:seeking p B)
    (hβ:0<β) (hz:0<η) (hη : playbook p K*η<1/2*β^2)
    (hd:∀ i,d i≤K^2) (he:∀ i,e i≤K^2):
    Guild.rich (stellar u s t η A B) := by
  classical
  intro i S hu y
  have hh a (b:Finset (Label p.b)) (h : b.card+902<Fintype.card (Label p.b)):
      ∃ z,z∉b∧z∉S a := by
    obtain ⟨z,hz⟩:=any_label (b∪S a) ((card_union_le ..).trans_lt ((Nat.add_le_add_left
      (hu a) _).trans_lt h))
    exact ⟨z,fun ht=>hz (mem_union_left _ ht),fun ht=>hz (mem_union_right _ ht)⟩
  obtain ⟨v,h1,h2⟩:= hh true (A i.1) (hk _)
  obtain ⟨w,h3,h4⟩:= hh false (B i.2) (hl _)
  let x : Zodiac p:= ⟨⟨0,by omega⟩,y.1,fun i=>if i then v else w,fun _=>Flavor.full⟩
  have hh : x.common:= fun i=> generic_apt p hg _ rfl
  obtain ⟨W,hA,hB,hC⟩:= sturdy_contact u s t h hs ht hβ x hh (fun _=>rfl) i y.2.1 y.2.2 hz
    ((mul_le_mul_of_nonneg_right (booklet_cap p K _ _ (hd _) (he _)) hz.le).trans_lt hη)
  refine ⟨(x,W),⟨⟨h1,h3,hA⟩,fun i=>?_⟩,?_⟩
  · cases i; exact h4; exact h2
  exact Prod.ext rfl (Prod.ext hB hC)

structure RhymeSet (d : ℕ) where
    bit : F
    coal : Cell d
    headBit : F
    gamma : F

def RhymeSet.read {k : ℕ} (s:RhymeSet k) (q:F) (x: Whole k) :=
    s.bit*x.2+ dotProduct s.coal x.1.2+ (s.bit+s.headBit)*x.1.1+s.gamma*q

def RhymeSet.soot {k : ℕ} (s:RhymeSet k) {p:Shape} (x:Appearance p) (y:Magazine p k) :=
    s.read x.q y.2

def leftChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (d i.1) :=
   ⟨q.left i.2,q.north i,q.hed i,0⟩
def rightChime (q:DualCoefficients d e) (i:Grid) : RhymeSet (e i.2) :=
   ⟨q.right i.1,q.south i,q.hed i,q.gam i⟩
set_option maxHeartbeats 900000 in
theorem dual_eq (q:DualCoefficients d e) (V : StatusSp d e) (hq:q.law V)
    (i:Grid) (x:Suite d e i) (hx:x∈V i) :
    (leftChime q i).read x.1 x.2.1=(rightChime q i).read x.1 x.2.2 := by
  classical
  specialize hq i x hx
  rcases x with ⟨a,⟨⟨b,u⟩,s⟩,⟨c,v⟩,t⟩
  let f:= q.hed i; let W:= dotProduct (q.north i) u
  let Z:= dotProduct (q.south i) v
  let g:=q.left i.2; let h:=q.right i.1; let G:=q.gam i*a
  change G+f*(b+c)+(W+Z)=g*(b+s)+h*(c+t) at hq
  change g*s+W+(g+f)*b+0*_ = h*t+Z+(h+f)*c+G
  apply sub_eq_zero.mp
  rw [ZModModule.sub_eq_add]
  calc _
      _=(G+f*(b+c)+(W+Z))+(g*(b+s)+h*(c+t)):=by ring
      _=0:= by rw [hq,char_two]

def charge (u:Terrain p r) (x: Zodiac p) (X:Gazette p r d) (Y:Gazette p r e)
    (i:Grid) (a:RhymeSet (d i.1)) (b:RhymeSet (e i.2)) :=
    pr (circlet u X Y x i) (fun y=>a.soot (x.aspect true) y.1≠ b.soot (x.aspect false) y.2)

def outstraps (a:Stalls p) (s:Straps (Label p.b)) (b:Bool):Stalls p:=
   fun i=>a i∪s b

set_option maxHeartbeats 900000 in
theorem charge_counter (h:origami p r u δ) (hs:reports p r u s β δ) (ht:reports p r u t β δ)
    (A B:Stalls p) (S : Straps (Label p.b)) (q:DualCoefficients d e)
    (he:q.law (chapter (stellar u s t η A B) S)) (hη:0≤η)
    (x: Zodiac p) (i:Grid) (hx:x.common) (hk:x.s true∉outstraps A S true i.1)
    (hl:x.s false∉outstraps B S false i.2) :
    charge u x s t i (leftChime q i) (rightChime q i)≤ num (Touch p d e i)*η := by
  classical
  let W:=circlet u s t x i
  obtain ⟨hm,hn⟩:=circlet_state u s t h hs ht x hx i
  let P:=fun y : Touch p d e i=> (leftChime q i).soot (x.aspect true) y.1≠
    (rightChime q i).soot (x.aspect false) y.2
  have hh (y): W y*ind (P y)≤η := by
    by_cases hp : P y
    · rw [ind_one hp,mul_one]
      by_contra! hy
      let C:=stellar u s t η A B
      let v : Scriptum p d e i := (x,y)
      have heq : (x.aspect true).fitsink y.1∧ (x.aspect false).fitsink y.2 := not_not.mp
        (fun h=> (hη.trans_lt hy).ne' (hn y h))
      have ht : (C i).zone S v :=
        ⟨⟨fun h=>hk (mem_union_left _ h),fun h=>hl (mem_union_left _ h),hx,heq.1,heq.2,hy.le⟩,
          fun i=>by cases i; exact fun h=>hl (mem_union_right _ h); exact fun h=>hk (mem_union_right _ h)⟩
      exact hp (dual_eq q (chapter C S) he i ((C i).writes v) ((C i).band_write S ht))
    rw [ind_zero hp,mul_zero]; exact hη
  change pr W P≤ _
  exact (Finset.sum_le_sum fun i _=> hh i).trans_eq (by simp [num])

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
