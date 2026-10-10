import OAI.Combinatorics.HadwigerCounterexample.PredictionClassBounds

namespace OAI

/-! # Compatible Pair Tests -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Module LinearMap Matrix
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p:Shape} {n N M r s0:ℕ}
    {w:rhythms p M} {b:PreparationParameters}

set_option maxHeartbeats 1800000 in
theorem foretold (w:rhythms p M) (m:cycleM p) (x:Sketch p M)
    (v:Station p n (M*n) b.pins (w n)) (hv:v.bank)
    (U:Wgt (UnitType p n (M*n))) (h:Lead U (w n) (m n) b)
    (hE:AnalyticParameters p M b s0)
    (hm:(w n).within (engrave x b m w n))
    (hn:2*p.r≤n) (Y:Silhouette p (M*n) r) (f:Bool→Pulsar p r)
    {τ ε δ η a d0:ℝ} (hh: hue x.c Y f (fun i=>x.g i n) x.α τ)
    (hε:0<ε) (hp:Jubilee p b.pins ε η)
    (hB:supportBudget p b.pins η a)
    (hz:x.ε n ≤scanPrice p*ε) (ht:10*ε≤τ) (hT:2*τ<1)
    (hF:Beams b (m n) Y (w n) U v a ε δ d0) (i : ViewPair p n (M*n) (w n))
    (hx:cirque (w n) U i ≠0)
    (hg1:gauze p δ δ Y (m n) b.pins i.1.2) (hg2:gauze p δ δ Y (m n) b.pins i.2.2)
    (hC:matchProg x n (i.1.2,i.2.2))
    (hS:secureAt p (w n).rooting (i.1.2,i.2.2)) :
    eligiblePair v (m n) i.1 i.2 Y a := by
  classical
  let s:=w n; let μ:= U; let K:=b.pins
  let X:=i.1.2; let Z:=i.2.2
  let j:=i.1.1; let k:=i.2.1
  let L:=troupe s μ
  have hs : L i.1≠0:=left_ne_zero_of_mul hx
  have hl : L i.2 ≠0:=right_ne_zero_of_mul hx
  have hX := troupe_home h i.1 hs
  have hZ:= troupe_home h i.2 hl
  have hL i:= (h.strength.leaf _ (Subtype.prop (show s.T from i))).bound
  obtain ⟨g,hg⟩:= ready_loupe s v hv hE hL
  let d:= g.r j; let e:=g.r k
  let t:=v.cAxes j (toRates d); let u:=v.cAxes k (toRates e)
  let A:=g.H j; let B:=g.H k
  let m':=x.m n
  let F:=x.L n X; let H:=x.L n Z
  let P:= A⊔F; let Q:=B⊔ H
  obtain ⟨⟨h1,h2⟩,h3,h4⟩:=hm _ j.property X hX.1
  obtain ⟨⟨h1',h2'⟩,h3',h4'⟩:=hm _ k.property Z hZ.1
  let M0:=s.pin j.val; let M1:=s.pin k.val
  have he (i):m' X i∈ effective M0.sp i:= (hX.2.1 ▸ (h1 i).2)
  have he' i:m' Z i∈effective M1.sp i:= (hZ.2.1 ▸ (h1' i).2)
  choose T hP using fun i=> show m' X i∈LinearMap.range (t i) from
    (hg.charts j i).1.symm ▸ he i
  choose S hQ using fun i=> show m' Z i∈ LinearMap.range (u i) from
    (hg.charts k i).1.symm ▸ he' i
  let Γ:PredictionData p (toRates d) (toRates e) r := ⟨x.α,f,T,S⟩
  have ht0:= hE.enter.first
  let M' := m n
  let D:=wisp p Y; let X0:=wake p Y M' X t; let X1:=wake p Y M' Z u
  let β:=trimBeta p K
  let C:=stellar D X0 X1 η P Q
  have hk0 i t:=Nat.lt_succ_iff.mp (g.r i t).isLt
  have hA: reports p r D X0 β δ:=routeLive s g v hg M' hE hn i.1 Y δ hF.haze.1 (hL _) hg1
  have hB1: reports p r D X1 β δ:=routeLive s g v hg M' hE hn i.2 Y δ hF.haze.1 (hL _) hg2
  have hR := boothseek b _ (g.H j) F (hg.baseline j) hE (fun i=>(h1 i).1)
  have hR' := boothseek b _ (g.H k) H (hg.baseline k) hE (fun i=>(h1' i).1)
  have hG: rich C:= plenitude hF.soft hA hB1 ht0.hG P Q hR hR' (trimBeta_pos ..) hp.pos
    hp.sturdyR (hk0 _) (hk0 _)
  obtain ⟨E,hE0,hr⟩:=stable C hG
  obtain ⟨y,hy⟩:= issueTicket X Z s v j k h.strength.part hX.1 hZ.1 hv hS
  let U0:=v.mails j k y
  have hQ': x.c.compatible x.α (glint p (m' X)) (cardTone m' X U0,cardTone m' Z
      (reciprocal p U0)) := by
    change glint p _=_ at h3
    have he1 l: cardTone m' X U0 l=(quench p (delta m') (X,Z)).1 l:=
      (fitsTone m' X hy.2.2 he l).trans (actualTone m' X Z l)
    have he2 l:cardTone m' Z (reciprocal p U0) l=(quench p (delta m') (X,Z)).2 l:= by
      have hg := fits_recip hy.2.2; rw [reciprocal_actual] at hg
      exact (fitsTone m' Z hg he' l).trans (actualTone m' Z X l)
    rw [funext he1,funext he2,h3]; exact hC
  have hc: countStory p K η δ ε β D:=⟨hF.soft,(trimBeta_pos ..).le,hε.le,hp.pos.le,
    hp.book,hp.low⟩
  have hv : Γ.colored D X0 X1 P Q (2*ε):= by
    constructor
    · exact crew_praise p x.c Y f (fun i=>x.g i n) x.α τ hh (m n) t T m' X F P le_sup_right
        hP hε.le hF.haze.2 hE hn (fun i j hj k f=>(h2 i j hj k f).trans hz) h4 hg1
    exact crew_praise p x.c Y f (fun i=>x.g i n) x.α τ hh (m n) u S m' Z H Q le_sup_right
      hQ hε.le hF.haze.2 hE hn (fun i j hj k f=>(h2' i j hj k f).trans hz) h4' hg2
  have hZ0 := laysScore p K Y (m n) D X Z m' (toRates d) (toRates e) t u x.c Γ P Q
    E η ε β δ τ hP hQ (paintChorus _ _ f _ x.α τ hh T S) (by linarith only [hε,ht]) hT hc
    hA hB1 hv (hk0 _) (hk0 _) ht0.hG ht hR hR' hE0 U0 (h3.trans h3'.symm) hQ' hG
  exact inform (w n) v _ Y i.1 i.2 hX.2.2.1 hZ.2.2.1 hX.2.2.2 hZ.2.2.2 d e (hg.charts _)
    (hg.charts _) hB A B (hg.baseline _) (hg.baseline _) P Q le_sup_left le_sup_left ht0.hG
    hE.jump hp.pos y hy E hr hZ0

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
