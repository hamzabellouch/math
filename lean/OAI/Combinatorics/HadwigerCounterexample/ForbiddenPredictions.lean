import OAI.Combinatorics.HadwigerCounterexample.FiniteComparisonBounds

namespace OAI

/-! # Forbidden Predictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Module LinearMap Finset Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p : Shape} {n N M r s0 K : ℕ} {w:LeafMixture p n N} {b:PreparationParameters}

def witnessed (w:LeafMixture p n N) (v:Station p n N K w) (L:Loupe p n N K w)
    (m:Mixer p n) (Y:Silhouette p N r)
    (δ ε:ℝ) (B:ℕ) (d:Dict p r) (x: Aspect p n N w) :=
  gauze p δ δ Y m K x.2 ∧ announced (wisp p Y) (wake p Y m x.2 (routeC w L v x)) d B ε

set_option maxHeartbeats 1200000 in
theorem witnessed_cost (w:LeafMixture p n N) (v:Station p n N b.pins w) (L:Loupe p n N b.pins w)
    (h:Shipped w b.pins v L)
    (m:Mixer p n) (Y:Silhouette p N r)
    (δ ε a:ℝ) (U:Wgt (UnitType p n N)) (d:Dict p r)
    (hp:Lead U w m b) (hq:AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (hδ:0≤δ) (he:0≤ε) (ht:(ε+δ)*2≤a)
    (hy:¬b.predicts p N m w U a) :
    pr (troupe w U) (witnessed w v L m Y δ ε b.B d) ≤ 0.001 := by
  classical
  let t:=troupe w U
  let F (i:Memo) := fun j=>fromPulse Y (Memo.words d i j)
  let P (i : Memo) (x : UnitType p n N):=∃ l B α,b.seems p m w x (F i) l B α a
  have hT:=troupe_bill hp
  have hi :
      pr t (fun i=>∃ j,P j i.2) ≤0.001 := by
    refine ((pr_exists_le hT.1.nz _).trans
      ((Finset.sum_le_sum (g:=fun _=>0.000001) fun i _ => ?_).trans ?_))
    · have hh : pr t (fun x=>P i x.2)=pr (w.sap U) (P i) := by
        rw [←hT.2,mapW_pr]
      rw [hh]; exact le_of_not_ge (fun he=> hy ⟨F i,he⟩)
    rw [Finset.sum_const,card_univ,memo_card]
    norm_num
  refine (pr_on_mono hT.1.nz ?_).trans hi
  rintro x hx ⟨hβ,i,q,r,S,hγ⟩
  let Q:=routeC w L v x
  have hm k:= praise_predict Q Y k x.2 m (q k) (r k) (Memo.words d i k)
    (S k) he hδ hq.enter.first.hR hn
    (fun z hz=> (hβ k z).1 hz) ((hγ k).2)
  have hh:=troupe_home hp x hx
  refine ⟨i,(fun i=>Q i (q i)), S,r,fun j=>⟨(hγ j).1,?_⟩,
     fun j i hi x v => (hm j i hi x v).trans ht⟩
  rw [hh.2.1,←(h.charts x.1 j).1]; exact mem_range_self _ _

set_option maxHeartbeats 2000000 in
theorem no_out (w:LeafMixture p n N) (b:PreparationParameters)
    (m:Mixer p n) (Y:Silhouette p N r) (U:Wgt (UnitType p n N))
    (v:Station p n N b.pins w) (ε η a δ τ:ℝ)
    (h:Lead U w m b) (ht:v.bank) (he:AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (hp:Jubilee p b.pins ε η) (hε:0<ε)
    (hB:supportBudget p b.pins η a)
    (hv:Beams b m Y w U v a ε δ (1/16))
    (hτ:(9*ε+ε)*2≤τ) (hh:¬b.predicts p N m w U τ)
    (hu:0.99 < pr (pairW (w.sap U) (w.sap U)) (secureAt p w.rooting)) :
    False := by
  classical
  let W:=Aspect p n N w; let K:=b.pins; let L:=troupe w U; let V:=cirque w U
  let u:=wisp p Y
  let β:=trimBeta p K
  let S (x:W):=gauze p δ δ Y m K x.2
  have hK i: planRank (w.pin (Subtype.val (show w.T from i))).sp ≤ K :=
    (h.strength.leaf _ i.property).bound
  obtain ⟨g,hg⟩:= ready_loupe w v ht he hK
  let f (x:W):=routeC w g v x
  let Q (x:W):=wake p Y m x.2 (f x)
  have ht' := he.enter.first
  have hd (x:W) (hx:S x) : reports p r u (Q x) β δ :=
    routeLive w g v hg m he hn x Y δ hv.haze.1 (hK x.1) hx
  have hL:2*b.B<Fintype.card (Label p.b) := by have hi:=he.spare; omega
  have hβ:=trimBeta_pos p K
  choose d hD using show ∀ x:W,∃ d:Dict p r,S x→anthology p r u (Q x) d b.B (3*ε) from by
    intro x
    by_cases hx:S x
    · obtain ⟨d,ht'⟩:= build_anthology u (Q x) hv.soft (hd x hx)
       (show 3*ε+3*ε<1/2*β by linarith only [show _ < 1/2*β from hp.low])
       hβ.le ht'.hG b.B hL
      exact ⟨d,fun _=>ht'⟩
    exact ⟨0,fun h=>(hx h).elim⟩
  let X (x:W×W):= secureAt p w.rooting (x.1.2,x.2.2)
  let Y1 (x:W×W):= witnessed w v g m Y δ (9*ε) b.B (d x.2) x.1
  let Y2 (x:W×W):= witnessed w v g m Y δ (9*ε) b.B (d x.1) x.2
  let Z (x:W×W):=¬ S x.1∨¬ S x.2
  let P (x:W×W):=eligiblePair v m x.1 x.2 Y a
  have hF:∀ i,V i ≠0 → X i→ ((Z i∨P i)∨ (Y1 i∨Y2 i)) := by
    intro i hi hk
    by_cases hQ:Z i∨P i
    · exact Or.inl hQ
    have ha1:S i.1:=not_not.mp (mt (fun x=>Or.inl (Or.inl x)) hQ)
    have ha2:S i.2:=not_not.mp (mt (fun x=>Or.inl (Or.inr x)) hQ)
    let A:=g.H i.1.1; let B:=g.H i.2.1
    let C:= stellar u (Q i.1) (Q i.2) η A B
    have hk0 (i t) := Nat.lt_succ_iff.mp (g.r i t).isLt
    have hz i:seeking p (g.H i):=by
      have h:= boothseek b _ (g.H i) ⊥ (hg.baseline i) he (fun _=>Nat.zero_le b.B)
      rwa [sup_bot_eq] at h
    have hC : rich C := plenitude hv.soft (hd _ ha1) (hd _ ha2) ht'.hG A B (hz _) (hz _)
      hβ hp.pos hp.sturdyR (hk0 _) (hk0 _)
    obtain ⟨E,hE,hI⟩:=stable C hC
    have hm0:= troupe_home h i.1 (left_ne_zero_of_mul hi)
    have hm1:= troupe_home h i.2 (right_ne_zero_of_mul hi)
    obtain ⟨k,hk⟩:= issueTicket _ _ w v i.1.1 i.2.1 h.strength.part hm0.1 hm1.1 ht hk
    let T:= v.mails i.1.1 i.2.1 k
    let R:= hailing p (f i.1) (f i.2) T
    by_cases hV:scorecard (chapter C E) R
    · exact (hQ (Or.inr (inform w v m Y i.1 i.2 hm0.2.2.1 hm1.2.2.1
        hm0.2.2.2 hm1.2.2.2 (g.r _) (g.r _) (hg.charts _) (hg.charts _) hB A B (hg.baseline _)
        (hg.baseline _) A B le_rfl le_rfl ht'.hG he.jump hp.pos k hk E hI hV))).elim
    obtain ⟨z,hz1,hz2,hz3⟩ := jargon_score _ _ hV (rich_covers C hC E (fun x=>(hE x).trans (by norm_num)))
    have hStory: countStory p K η δ ε β u:=⟨hv.soft,hβ.le,hε.le,hp.pos.le,hp.book,hp.low⟩
    let G0:=outstraps A E true; let G1:=outstraps B E false
    have hE0 (j):= outcard p A E (hz _) hE true j
    have hE1 (j):= outcard p B E (hz _) hE false j
    have hT:= tells z hStory (hd _ ha1) (hd _ ha2) A B E hz2 (hk0 _) (hk0 _) hE0 hE1 ht'.hG
    have hu i (j k:Bool): (outstraps (g.H i) E j k).card≤ b.B:= by
      refine (card_union_le ..).trans ?_
      have hi:=(hg.baseline i).1 k; have hh:= hE j; have hx:= he.forbid; omega
    right
    have hh:=quotes (d i.1) (d i.2) (hd _ ha1) (hd _ ha2) hv.soft z hz1 G0 G1 hT b.B
      (hD _ ha1) (hD _ ha2) (hu _ _) (hu _ _)
    rw [show 3*(3*ε)=9*ε from by ring] at hh
    exact hh.elim (fun h=>Or.inl ⟨ha1,h⟩) (fun h=>Or.inr ⟨ha2,h⟩)
  have hL:IsLaw L:= (troupe_bill h).1
  have hz0 (i:W): pr L (witnessed w v g m Y δ (9*ε) b.B (d i)) ≤ 0.001 :=
    witnessed_cost w v g hg m Y δ (9*ε) τ U (d i) h he hn hv.haze.1.le (by linarith)
      (by linarith only [hτ,hv.haze.2]) hh
  have hZ1: pr V Y1 ≤ 0.001 := by
    unfold pr V cirque; rw [pairW_avg,avg_avg]; exact hL.avg_le hz0
  have hZ2: pr V Y2 ≤0.001 := by unfold pr V cirque; rw [pairW_avg]; exact hL.avg_le hz0
  have hO:IsLaw V:=pairW_law hL hL
  have hX :0.99 < pr V X := by rw [←cirque_unit _ h,mapW_pr] at hu; exact hu
  have hP:= show pr V P≤1/16 from hv.zone
  have hZ:= show pr V Z ≤ 1/16+1/16 from (sickBound U v Y h _ _ _ _ hv).2
  have hx: pr V X≤(1/16+1/16+1/16)+(0.001+0.001):=
    ((pr_on_mono hO.nz hF).trans (pr_or_le hO.nz)).trans
      (add_le_add ((pr_or_le hO.nz).trans (add_le_add hZ hP)) ((pr_or_le hO.nz).trans
        (add_le_add hZ1 hZ2)))
  linarith only [hX,hx]
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
