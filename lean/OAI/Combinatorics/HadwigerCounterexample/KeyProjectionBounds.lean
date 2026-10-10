import OAI.Combinatorics.HadwigerCounterexample.UniformLeafComparisons

namespace OAI

/-! # Key Projection Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap
open scoped BigOperators Topology
variable {p:Shape} {n N M K r s0 : ℕ}
namespace StatusAnalysis
open Station
namespace Station
variable {q:Format} {d e:Rates} {w : LeafMixture p n N} (t : Station p n N K w)
    (x:Typus p q d e) (m:Mixer p n) (μ:Wgt (UnitType p n N)) (k:Fin (2^deckMax p K))
    (Y:Silhouette p N r)

variable {B : Type} [Fintype B]
def taxLeft (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageLeft t x m μ k Y i j a) P)
      (mapW (t.leftSales x m μ i j k) P)
def taxRight (P : Keys (p:=p) x.t N →B) (i j : w.T) :=
    varOne (mapW (fun a=> lawNu p N x.t x.z a * stageRight t x m μ k Y i j a) P)
      (mapW (t.rightSales x m μ i j k) P)
def due (P : Keys (p:=p) x.t N→B) :=
    avg (pairW (portionW μ w.T) (portionW μ w.T)) (fun i=>
       taxLeft t x m μ k Y P i.1 i.2+taxRight t x m μ k Y P i.1 i.2)
def dueEnough {l:ℕ} (ε η:ℝ) (P : Keys (p:=p) x.t N→ Fin l) :=
    ∀ r:ℕ,∀ Y:Silhouette p N r, due t x m μ k Y P ≤ η → stratum t x m μ k Y ≤ ε
end Station

open PreparationParameters
variable {l:Filter ℕ} {b:PreparationParameters} {m:cycleM p} {s : rhythms p M} {w:tale p M}

set_option maxHeartbeats 1800000 in
theorem projectCut {q:Format} {d e:Rates} (x:Typus p q d e)
    (h:x.permission)
    (k:Fin (2^deckMax p b.pins))
    (hv:veil p M b s0 l m s w) (t:Stations p M b.pins s)
    (ε:ℝ) (he:0<ε) :
    ∃ (r:ℕ) (η:ℝ), 0<η∧∀ᶠ n in l, let N:=M*n;
      ∃ P:Keys (p:=p) x.t N→Fin r,
      dueEnough (t n) x (m n) (w n) k ε η P := by
  classical
  let H := (ε/2)^2/8
  have hH : 0<H:=by unfold H; positivity
  have hE:=hv.easel
  have ht:=hE.enter.first
  obtain ⟨Ra,ha,hA⟩:= x.qA.pennywise x.t x.z M hE h.2.1 H hH
  obtain ⟨Rb,hβ,hB⟩:= x.qB.pennywise x.t x.z M hE h.2.2.1 H hH
  let R:= max Ra Rb
  have hr :0<R:=lt_max_of_lt_left ha
  obtain ⟨δ,hd,hG⟩:=global_net R H hr hH
  obtain ⟨a,hJ⟩:=hA δ hd; obtain ⟨b1,hY⟩:=hB δ hd
  obtain ⟨r,hk⟩:=hG (max a b1)
  obtain ⟨u,hu,hd'⟩:=veil.score_cost hv t
  refine ⟨r,H,hH,?_⟩
  have hl:= hv.timeL
  have hz:=(trend_sizes l hl ht.hM).2
  let L:= 2*netFact (trayPort p x.t)
  have hg : ∀ᶠ n in l, L*bp (-((M*n:ℕ):ℝ)/2)≤ ε/2 := by
    have hx:=(((bp_tendsto_zero (by norm_num : 0<(1/2:ℝ))).comp hz).const_mul L)
    have heq : ∀ᶠ n in l,L*bp (-(1/2:ℝ)*((M*n:ℕ):ℝ))≤ ε/2 :=
      hx.eventually (eventually_le_nhds (by rw [mul_zero]; linarith only [he]))
    filter_upwards [heq] with n hn; rw [show -((M*n:ℕ):ℝ)/2= -(1/2:ℝ)*((M*n:ℕ):ℝ) from by ring]; exact hn
  filter_upwards [hv.upright,hv.moment, hv.durableS.mass.positive,hv.durableS.shape,hJ.filter_mono hl,
    hY.filter_mono hl,hd',(hu.lim hz).eventually (eventually_le_nhds hH),hg,
    hz.eventually (eventually_ge_atTop (2*num (Messenger q×Toast p)+1))]
    with n hn ht' hm he' hx hy hh h' hR hN N
  let v:= t n
  let w':=w n; let s':= s n
  let I := s'.T
  let F (i : ↑I):= partW w' i.val
  let A (i : ↑I) := x.qA.custom (F i) (v.cAxes i d) x.t x.z (m n)
  let B (i : ↑I) := x.qB.custom (F i) (v.cAxes i e) x.t x.z (m n)
  let u:=portionW w' I; let ν:=lawNu p N x.t x.z
  have ht0 : IsLaw w':=ht'.1.law
  have hF i (hi : i∈I): IsLaw (partW w' i):= on_law ht0.nz
    (he'.1.leaf i hi).pos
  have hX i (hi : i∈I) := (he'.1.leaf _ hi).density
  have hA' (i:↑I) :
      x.qA.penny x.t x.z (m n) (v.cAxes i d) (F i) R H δ (max a b1) :=
    Quill.pennyLarge x.qA x.t x.z _ _ _ _ _ _ _ (hx (m n) _ (F i) hn.cols (hF _ i.property)
      (hX _ i.property)) (le_max_left ..) (le_max_left ..)
  have hB' (i:↑I) : x.qB.penny x.t x.z (m n) (v.cAxes i e) (F i) R H δ (max a b1) :=
    Quill.pennyLarge x.qB x.t x.z _ _ _ _ _ _ _ (hy (m n) _ (F i) hn.cols (hF _ i.property)
      (hX _ i.property)) (le_max_right ..) (le_max_right ..)
  have hu :IsLaw u := (rebuild ht0.nz he'.1.part (fun i hi=>(he'.1.leaf _ hi).pos) hm).1
  have hhN : 2*num (Messenger q×Toast p)-(N:ℝ)≤ -1 := by
    change _≤(N:ℝ) at hN; linarith only [hN]
  have hν : IsLaw ν := nuLaw x.t x.z hhN
  obtain ⟨j,hj,P,hP⟩:= hk (↑I) (↑I) (Keys (p:=p) x.t N) u u ν hu hu hν A B
    (fun i=>(hA' i).roll) (fun i=>(hB' i).roll)
  let Q := (Fin.castLE hj) ∘ P
  refine ⟨Q,fun z Y hs=>?_⟩
  let W := pairW u u
  have hW:=pairW_law hu hu
  let L := fun x':↑I×↑I =>t n|>.leftSales x (m n) (w n) x'.1 x'.2 k
  let U' := fun x':↑I×↑I =>t n|>.rightSales x (m n) (w n) x'.1 x'.2 k

  have hχ (i:↑I×↑I) : A i.1 (L i) := x.qA.sales_custom _ _ _ _ _ _
  have hν' (i:↑I×↑I) : B i.2 (U' i) := x.qB.sales_custom _ _ _ _ _ _
  let J(i:↑I×↑I):=|rebate ν (mcut R ν (L i)) (mcut R ν (U' i)) Q|
  have he1 :
      avg W J≤H := by
    unfold J Q; simp_rw [rebate_thick ν _ _ (Fin.castLE_injective hj)]; exact hP L U' hχ hν'
  let g := fun i : ↑I×↑I=> stagePlane v x (m n) (w n) k Y i.1 i.2
  let f := fun i : ↑I×↑I=> Station.eclipse v x (m n) (w n) k Y i.1 i.2
  let C := fun i : ↑I×↑I=> matchScore v x (m n) (w n) i.1 i.2 k
  let D := fun i:↑I×↑I=> taxLeft v x (m n) (w n) k Y Q i.1 i.2+taxRight v x
    (m n) (w n) k Y Q i.1 i.2
  have hA1 i : IsLaw (x.qA.policies x.t x.z n i) :=
    Appearance.witLaw (x.qA.allure_apt _ _ h.2.1 _) ht.hR hn.age
  have hB1 i : IsLaw (x.qB.policies x.t x.z n i) :=
    Appearance.witLaw (x.qB.allure_apt _ _ h.2.2.1 _) ht.hR hn.age
  let X i:= C i+J i+D i+(2*H)
  have hP : ∀ i,g i^2≤ X i := by
    intro i
    let A' := stageLeft v x (m n) (w n) k Y i.1 i.2
    let B' := stageRight v x (m n) (w n) k Y i.1 i.2
    have hh := hχ i; have hk:= hν' i
    obtain ⟨h1,h2⟩:= (hA' _).sales _ hh
    obtain ⟨h3,h4⟩:= (hB' _).sales _ hk
    have h := density_mend ν hν Q R hr.le A' B' (L i) (U' i) (x.qA.bower_case _ _ _ _ _ _ _ (hF _ i.1.property)
      hA1) (x.qB.bower_case _ _ _ _ _ _ _ (hF _ i.2.property) hB1) h1 h3 h2 h4
    have he1 : trayLoss R ν (L i) ≤ H := (hA' _).tailS _ hh
    have he2 : trayLoss R ν (U' i)≤ H := (hB' _).tailS _ hk
    let a:=taxLeft v x (m n) (w n) k Y Q i.1 i.2
    let b0:=taxRight v x (m n) (w n) k Y Q i.1 i.2
    change g i^2 ≤ C i+ J i+(a+trayLoss R ν (L i)+(b0+trayLoss R ν (U' i))) at h
    change _ ≤ C i+J i+(a+b0)+2*H
    linarith only [he1,he2,h]
  refine skylineMean W f g X ε he.le hW ?_ hP (fun i=> (eclipse_beam v x (m n) (w n)
    k Y i.1 i.2 hF hA1 hB1 hhN).trans hR)
  have hc : avg W C≤ H := le_trans ((le_abs_self _).trans (hh q d e x k)) h'
  unfold X; rw [avg_add,avg_add,avg_add]
  have hj : avg W (fun _=> 2*H)=2*H := hW.avg_const _
  rw [hj]
  change avg W D≤ H at hs
  rw [show (ε/2)^2=8*H from by unfold H; ring]; linarith only [hc,he1,hs,hH]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
