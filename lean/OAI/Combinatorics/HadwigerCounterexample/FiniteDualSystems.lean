import OAI.Combinatorics.HadwigerCounterexample.IncompatibleMassBounds

namespace OAI

/-! # Finite Dual Systems -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Function LinearMap Module
open scoped BigOperators Topology
open Template
variable {p : Shape} {N n r K : ℕ}
namespace StatusAnalysis

/-- envelope information to certify a generator, shared l and q. -/
structure Zodiac (p : Shape) where
  l : Tag p.g
  q : F
  s : Bool → Label p.b
  f : Bool→Flavor p.g

namespace Zodiac
def aspect (w : Zodiac p) (b : Bool) : Appearance p :=
  ⟨w.l,w.s b,w.f b,w.q⟩
def common (w : Zodiac p) := ∀ b,(w.aspect b).apt
end Zodiac
instance zodiac_dec (p:Shape): DecidableEq (Zodiac p) := Classical.typeDecidableEq _

abbrev Terrain (p:Shape) (r:ℕ):= Tag p.g → F → Wgt (Fin r)
abbrev Gazette (p:Shape) (r:ℕ) (d : Rates) :=
   (i:Nodes)→Appearance p → Fin r→ Wgt (Magazine p (d i))

variable {d e : Rates}
namespace DualAnalysis

def wisp (p : Shape) (Y : Silhouette p N r) : Terrain p r :=
 fun i z => mapW (lawOmega p N i z) (Y i z)
def wake (p : Shape) (Y : Silhouette p N r) (m:Mixer p n) (o:UnitType p n N)
    (s : Charts p n d) : Gazette p r d :=
 fun i x a=> x.reflected Y i o m (s i) a
def parcelOrg (A:Stalls p) (i:Nodes) (a:Appearance p) := a.s∉ A i

def origami (p:Shape) (r:ℕ) (u:Terrain p r) (δ:ℝ) :=
   (∀ i q,IsLaw (u i q)) ∧ ∀ i q,1/2 ≤ pr (u i q) (fun x=>δ ≤ u i q x)
structure reports (p:Shape) (r:ℕ) (u:Terrain p r) (s:Gazette p r d)
    (β δ:ℝ) : Prop where
  law : ∀ i (x:Appearance p),x.apt → ∀ k:Fin r,IsLaw (s i x k)
  supp : ∀ i (x:Appearance p),x.apt →∀ k,carried (s i x k) x.fitsink
  generous : ∀ i (x:Appearance p), x.f=Flavor.full → x.apt →
     ∀ k:Fin r,δ ≤ u x.l x.q k → ∀ v: Par (d i),
       β ≤ pr (s i x k) (fun w=>w.2.1=v)

def playbook (p : Shape) (K : ℕ) := num (Magazine p (K^2) × Magazine p (K^2))

theorem playbook_pos (p : Shape) (K : ℕ) : 0 < playbook p K := by unfold playbook num; positivity
theorem booklet_cap (p:Shape) (K d e:ℕ) (hd:d≤K^2) (he:e≤K^2) :
    num (Magazine p d × Magazine p e) ≤ playbook p K := by
  have ht (d e) (h:d≤e) :
      Fintype.card (Magazine p d) ≤ Fintype.card (Magazine p e) := by
    simp only [Magazine,Whole,Par,Fintype.card_prod,Cell,Vec,Fintype.card_fun,Fintype.card_fin]
    have hF:0<Fintype.card F := Fintype.card_pos
    gcongr
  unfold num playbook num
  exact_mod_cast (show Fintype.card (Magazine p d × Magazine p e) ≤ _ from by
    simpa only [Fintype.card_prod] using Nat.mul_le_mul (ht _ _ hd) (ht _ _ he))

theorem plume_reports (p:Shape) (K :ℕ) (m:Mixer p n) (Y:Silhouette p N r)
    (s:Plan p n) (t:Charts p n d) (o:UnitType p n N)
    (hs:charted t s) (hh:∀ i,d i≤K^2) (h:planRank s≤K)
    (hg:3≤p.g) (hp:1≤p.r) (hn:2*p.r≤n) (δ:ℝ) (hδ:0<δ)
    (hY:gauze p δ δ Y m K o):
    reports p r (wisp p Y) (wake p Y m o t) (basebeta p K/2) δ := by
  constructor
  · intro i x hx k; exact x.reflectedLaw Y (Appearance.witLaw hx hp hn) _ _ _ _ _
  · intro i x hx k; exact x.refInk Y _ _ _ _ _
  intro i x hx he k hk v
  obtain ⟨g,ha,hb,hc⟩:=generic_summary p hg x.l x.q v.1
  rw [←hx] at ha
  have hf:= x.demonstrates Y o (m:=m) (t i) K i k δ hδ g v.2 ha hb hp hn hk (hY _)
    (hh _) (hs i).2 (fun x=>le_trans (effective_rank (i:=i) (s:=s) (by rw [←(hs i).1]; exact mem_range_self _ _)) h)
  exact hf.trans (pr_mono (x.reflectedLaw Y (Appearance.witLaw he hp hn) i o m (t i) k).nz
    (fun j hj=>hj.2.trans (Prod.ext hc rfl)))

abbrev Scriptum (p:Shape) (d e: Rates) (i : Grid) :=
   Zodiac p × Magazine p (d i.1) × Magazine p (e i.2)
abbrev Touch (p:Shape) (d e : Rates) (i : Grid) := Magazine p (d i.1) × Magazine p (e i.2)
variable (u:Terrain p r) (s:Gazette p r d) (t:Gazette p r e)
  (η:ℝ)
def couplePage (x:Zodiac p) (i:Grid) :=
    fun j:Fin r=> pairW (s i.1 (x.aspect true) j) (t i.2 (x.aspect false) j)
def circlet (x:Zodiac p) (i:Grid) : Wgt (Touch p d e i) :=
    mixW (u x.l x.q) (couplePage s t x i)
def eligible (x:Zodiac p) (i:Grid) (a : Touch p d e i) :=
    x.common ∧ (x.aspect true).fitsink a.1 ∧ (x.aspect false).fitsink a.2 ∧
      η ≤ circlet u s t x i a
def stellar (A B : Stalls p) : Congress (Scriptum p d e) d e (Label p.b) :=
    fun i=> {
      valid x:= x.1.s true∉ A i.1 ∧ x.1.s false∉ B i.2 ∧ eligible u s t η x.1 i x.2
      writes x:= (x.1.q,x.2.1.2,x.2.2.2)
      addr x:= x.1.s
    }

variable {β δ:ℝ}
theorem circlet_state (hu:origami p r u δ) (hs:reports p r u s β δ)
    (ht:reports p r u t β δ)
    (x: Zodiac p) (hx:x.common) (i:Grid):
    IsLaw (circlet u s t x i) ∧ carried (circlet u s t x i)
      (fun y=>(x.aspect true).fitsink y.1 ∧ (x.aspect false).fitsink y.2) := by
  have hh := hu.1 x.l x.q
  refine ⟨mixW_law hh (fun _=>pairW_law (hs.law _ _ (hx _) _) (ht.law _ _ (hx _) _)),?_⟩
  intro y hy
  have hi j : couplePage s t x i j y=0 := by
    by_cases h :(x.aspect true).fitsink y.1
    · unfold couplePage pairW
      rw [ht.supp _ _ (hx _) j _ (fun hh=>hy ⟨h,hh⟩),mul_zero]
    unfold couplePage pairW; rw [hs.supp _ _ (hx _) j y.1 h,zero_mul]
  unfold circlet mixW
  simp_rw [hi,avg_const,mul_zero]

set_option maxHeartbeats 1000000 in
theorem sturdy_contact (hu:origami p r u δ) (hs:reports p r u s β δ)
    (ht:reports p r u t β δ) (hβ:0<β)
    (x: Zodiac p) (hx:x.common) (h:∀ i, x.f i=Flavor.full)
    (i: Grid) (L: Par (d i.1)) (R: Par (e i.2))
    {η:ℝ} (he:0<η) (hη:num (Touch p d e i)*η < 1/2*β^2):
    ∃ j : Touch p d e i, eligible u s t η x i j ∧ j.1.2.1=L∧ j.2.2.1=R := by
  classical
  obtain ⟨hF,hG⟩:= circlet_state u s t hu hs ht x hx i
  let μ:=u x.l x.q
  let Q j:=δ≤μ j
  let Z (j:Touch p d e i):=j.1.2.1=L∧ j.2.2.1=R
  let W:=circlet u s t x i
  have hh:1/2*β^2 ≤ pr W Z := by
    let g:= couplePage s t x i
    have hh : pr W Z=avg μ (fun j=>pr (g j) Z):= mixW_avg ..
    have heq j (hj : Q j) :
       β^2≤ pr (g j) Z := by
      rw [pow_two]
      let P0 (x:Magazine p (d i.1)):= x.2.1=L
      let Q0 (x:Magazine p (e i.2)):= x.2.1=R
      have he := pairW_pr (s i.1 (x.aspect true) j) (t i.2 (x.aspect false) j) P0 Q0
      have hh:=hs.generous i.1 (x.aspect true) (h _) (hx _) j hj L
      exact (mul_le_mul hh (ht.generous i.2 (x.aspect false) (h _) (hx _) j hj R) hβ.le
        (hβ.le.trans hh)).trans_eq he.symm
    refine (mul_le_mul_of_nonneg_right (hu.2 x.l x.q) (sq_nonneg _)).trans ?_
    rw [hh]; unfold pr; rw [←avg_mul]; refine avg_mono (hu.1 _ _).nz (fun j=> ?_)
    change ind (Q j) * β^2 ≤ pr (g j) Z
    by_cases hj:Q j
    · rw [ind_one hj,one_mul]; exact heq _ hj
    rw [ind_zero hj,zero_mul]
    exact pr_nonneg (pairW_law (hs.law _ _ (hx _) j) (ht.law _ _ (hx _) j)).nz
  by_contra! hv
  have hg j : W j * ind (Z j) ≤ η := by
    by_cases h:Z j
    · rw [ind_one h,mul_one]
      by_contra! he'
      have hc : W j≠0:=(he.trans he').ne'
      have h1 : (x.aspect true).fitsink j.1∧(x.aspect false).fitsink j.2 :=
        not_not.mp fun h=> hc (hG _ h)
      exact hv _ ⟨hx,h1.1,h1.2,he'.le⟩ h.1 h.2
    rw [ind_zero h,mul_zero]; exact he.le
  apply hη.not_ge; exact hh.trans ((Finset.sum_le_sum fun i _=>hg i).trans_eq (by simp [num]))

end DualAnalysis
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
