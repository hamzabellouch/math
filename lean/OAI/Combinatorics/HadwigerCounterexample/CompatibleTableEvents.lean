import OAI.Combinatorics.HadwigerCounterexample.RareTestEvents

namespace OAI

/-! # Compatible Table Events -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters PredictionClass

variable {p:Shape} {n M K s0 N :ℕ} {w:LeafMixture p n N} {q:PreparationParameters}

structure Settled (t: LeafMixture p n N) (m:Mixer p n) (q:PreparationParameters)
    (U : Wgt (UnitType p n N)) (z:BMark p n N) (k:F) : Prop where
    readyC :
    IsLaw U ∧ t.strength U (usual p m N) q.leafNew (2*q.ζ) q.pins ∧
    t.within (fun o=>frameSide p m o ∧ exactInk p m z o ∧
       (∀ i,z o i∈effective (t.rooting o) i) ∧ glint p (z o)=k)
    hard : q.hardened p N t z

def shimmer (z:BMark p n N) (r:F) (x:UnitType p n N× UnitType p n N) :=
   quench p (delta z) x=repeatQ r

variable (v: Station p n N q.pins w) (i j:w.T)
    (U:Wgt (UnitType p n N)) (m:Mixer p n) (z:BMark p n N)

private theorem chartKnown {r : F} (q:PreparationParameters) (x:w.T) (d: Stakes q.pins)
    (hw:Settled w m q U z r)
    {v : Charts p n (toRates d)} (hc:charted v (w.pin x.val).sp)
    (o : UnitType p n N) (hx:o∈x.val) :
    (∀ i,totalRank (z o i)≤ q.pins) ∧ ∃ y,∀ i∈x.val,coordSpec z i v y := by
  obtain ⟨h1,h2,h3⟩:=hw.readyC
  let A:=(w.pin x.val).sp
  have hi j : z o j∈effective A j := by
    have hh : w.rooting o=A:=congrArg Pin.sp (LeafMixture.poller_eq w h2.part x.property hx)
    rw [←hh]; exact (h3 x.val x.property o hx).2.2.1 j
  obtain ⟨T,hK,hB,hG⟩:=hw.hard
  obtain ⟨b,hb,hf⟩:=hG x.val x.property
  choose y hy using fun j=> show z o j∈LinearMap.range (v j) from (hc j).1.symm ▸ hi j
  refine ⟨fun i=>(effective_rank (hi i)).trans (h2.leaf x.val x.property).bound,y,
    fun i hh j=>?_⟩
  exact (hy j).trans (congr_fun (hb.2.2 _ hx _ hh).1 j)

set_option maxHeartbeats 1800000 in
theorem invoke (k:Fin (2^deckMax p q.pins))
    (r:F) (a:ℝ) (hα:0<a) (h:AnalyticParameters p M q s0)
    (hw:Settled w m q U z r) (ht:v.bank)
    (hk:2*a ≤ pr (pairW (partW U i.val) (partW U j.val))
       (fun x=> shimmer z r x∧ berthTicket (w.pin i.val) (w.pin j.val) (v.mails i j k) x)) :
    ∃ x:Scrip p q.pins, v.charter x.2.2 m x.2.1 U a (i,j) := by
  classical
  let K:=q.pins
  let T:=v.mails i j k
  have hq:=h.enter.first
  let a0:= w.pin i.val; let b0:= w.pin j.val
  let μ i:=partW U (Subtype.val (show w.T from i))
  let S:=pairW (μ i) (μ j)
  obtain ⟨hm,hv,hC⟩:=hw.readyC
  have hu x:=show IsLaw (μ x) from on_law hm.nz (hv.leaf x.val x.property).pos
  have hμ: IsLaw S:= pairW_law (hu _) (hu _)
  have hK x : planRank (w.pin (Subtype.val (show w.T from x))).sp ≤ K :=
    (hv.leaf _ (Subtype.prop x)).bound
  obtain ⟨f,hF⟩:=sizedCharts q.pins w v ht i (hK i)
  obtain ⟨g,hG⟩:=sizedCharts q.pins w v ht j (hK j)
  let A:= toRates f; let B:=toRates g; let X:=v.cAxes i A; let Y:=v.cAxes j B
  let P x:= shimmer z r x∧ berthTicket a0 b0 T x
  obtain ⟨o,⟨hop,hOK⟩,ho⟩:= exists_of_pr_pos hμ.nz (lt_of_lt_of_le
    (show 0<2*a by positivity) hk)
  let x:=o.1; let y:=o.2
  have hcol i x (hx:μ i x≠0) : x∈ i.val := (onW_ne hx).1
  have hx : x∈ i.val:= hcol i x (left_ne_zero_of_mul ho.ne')
  have hy : y∈ j.val:= hcol j y (right_ne_zero_of_mul ho.ne')
  obtain ⟨hχ,l,hl⟩:= chartKnown (v:=X) U m z q i f hw hF x hx
  obtain ⟨hξ,t,ht'⟩:= chartKnown (v:=Y) U m z q j g hw hG y hy
  have he (i : w.T) x (hx:x∈ i.val) : ∀ j,z x j∈effective (w.pin i.val).sp j := by
    have hi : w.rooting x=(w.pin i.val).sp:=congrArg Pin.sp (LeafMixture.poller_eq w hv.part i.property hx)
    rw [← hi]; exact (hC _ i.property _ hx).2.2.1
  let kappa : Tag p.g:= ⟨0,by linarith only [hq.hG]⟩
  let tt : Tagging p (Messenger singles):=fun _=>kappa
  let ref := show Messenger singles→F from fun _=>1
  obtain ⟨E,h1,h2,h3⟩:= generic_summary p hq.hG kappa 1 0
  obtain ⟨H,h4,h5,h6⟩:= generic_summary p hq.hG kappa 1 1
  obtain ⟨L,hLa⟩:= buildBooths K a0.sp (hK i) h.penRoom
  obtain ⟨O,hLb⟩:= buildBooths K b0.sp (hK j) h.penRoom
  have hh : 2*frameBills p.g K+4 ≤ Fintype.card (Label p.b) := by
    have hl : frameBills p.g K + 1000 ≤ q.B:=h.forbid
    have he:= h.spare; omega
  obtain ⟨J,hJ,hJ'⟩:= fourPens _ K L hLa hh
  obtain ⟨I,hI,hI'⟩:= fourPens _ K O hLb hh
  let F0:Fabric p singles A true:=⟨J,fun _ => Flavor.full,beacon p X l true T E⟩
  let T':= reciprocal p T
  let G0:Fabric p singles B false:=⟨I,fun _=> Flavor.full,beacon p Y t false T' H⟩
  have hs : speak A B (sendSum ref F0.amp G0.amp)=(hailing p X Y T,0) := by
    apply (spoken X Y T ref F0.amp G0.amp).mpr
    have hFq a : fullq ref a=1 := by
      unfold fullq
      change (∑ _:Fin 1,(1:F))=1; rw [Fintype.sum_unique]
    have hR : rhyme F0.amp G0.amp := by
      intro i; have hf : (funds F0.amp i).1.1=E.diagO := congrArg (fun x=> x.1.1) (funds_one F0 i)
      have hg : (funds G0.amp i).1.1=H.diagO := congrArg (fun x=> x.1.1) (funds_one G0 i)
      change (funds (b:=true) F0.amp i).1.1+(funds (b:=false) G0.amp i).1.1=_; rw [hf,hg,h3,h6,zero_add]
    refine ⟨hFq,hR, stillBeacon z x X l true T E (hl _ hx) (fun k=>?_),stillBeacon z y Y t false
      T' H (ht' _ hy) (fun k=>?_)⟩
    · rw [fitsTone z x hOK.2.2 (he _ _ hx), actualTone,(hC _ i.property _ hx).2.2.2]
      exact congr_fun (congrArg Prod.fst hop) k
    have hg:=fits_recip hOK.2.2; rw [reciprocal_actual] at hg
    rw [fitsTone z y hg (he _ _ hy), actualTone,(hC _ j.property _ hy).2.2.2]
    exact congr_fun (congrArg Prod.snd hop) k
  obtain ⟨P0,Q0,hf⟩:= optionVia singles A B a0 b0 T K hOK.1 hOK.2.1 tt X Y hF hG F0 G0 L O hLa hLb
    (fun i=>hJ' i _) (fun i=> hI' i _) ref ⟨hJ,fun i=>h2,fun i=>h1⟩
    ⟨hI,fun i=>h5,fun i=>h4⟩ h.jump (by linarith only [hq.hG]) singles_short hs
  let τ:Typus p singles A B:= ⟨tt,ref,F0.hang P0,G0.hang Q0⟩
  let Front:=v.frontPage τ m i j k; let Back:=v.backPage τ m i j k
  have hi a (ha:a∈ i.val): a0.agree a := (hv.leaf _ i.property).fixpin _ ha
  have hi' a (ha:a∈ j.val): b0.agree a := (hv.leaf _ j.property).fixpin _ ha
  have hm : 2*a≤ (pr (μ i) Front)*(pr (μ j) Back) := by
    rw [←pairW_pr]
    apply hk.trans
    refine pr_on_mono hμ.nz (fun x hx he=>?_)
    have h1 := hcol i x.1 (left_ne_zero_of_mul hx)
    have h2 := hcol j x.2 (right_ne_zero_of_mul hx)
    obtain ⟨ha,hb⟩:= berth_flags a0 b0 T he.2 (hi _ h1) (hi' _ h2)
    exact ⟨⟨hf,hi _ h1,(hC _ i.property x.1 h1).1, ha⟩,
      ⟨hf,hi' _ h2,(hC _ j.property _ h2).1,hb⟩⟩
  refine ⟨⟨(volume1,f,g),k,show OnFile p _ from τ⟩,hf.1,⟨?_,fun o ho hx=>?_⟩,
    ⟨?_,fun o ho hx=>?_⟩⟩
  · exact hm.trans ((mul_le_mul_of_nonneg_left ((pr_le_tot (hu _).nz).trans (hu j).total.le)
      (pr_nonneg (hu _).nz)).trans_eq (mul_one _))
  · have hv := hcol i o hx
    exact steadyBeacon z o X l true T τ.qA tt m E K
      (fun x=> Nat.lt_succ_iff.mp (f x).isLt) rfl (hK i) hF (hl _ hv) ho.2.2.1
      (hC _ i.property _ hv).2.1
  · exact hm.trans ((mul_le_mul_of_nonneg_right ((pr_le_tot (hu _).nz).trans (hu i).total.le)
      (pr_nonneg (hu _).nz)).trans_eq (one_mul _))
  have hv:=hcol j o hx
  exact steadyBeacon z o Y t false T' τ.qB tt m H K
    (fun x=> Nat.lt_succ_iff.mp (g x).isLt) rfl (hK j) hG (ht' _ hv) ho.2.2.1
    (hC _ j.property _ hv).2.1

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
