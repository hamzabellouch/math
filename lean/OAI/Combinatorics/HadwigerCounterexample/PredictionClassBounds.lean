import OAI.Combinatorics.HadwigerCounterexample.ForbiddenPredictions

namespace OAI

/-! # Prediction Class Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Function Module LinearMap Matrix
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M K s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild
variable {w:LeafMixture p n N} {b:PreparationParameters} {B:Sketch p M}
variable {d e: Rates}

set_option maxHeartbeats 1200000 in
theorem laysScore (p:Shape) (K:ℕ)
    (Y: Silhouette p N r) (m: Mixer p n) (U:Terrain p r)
    (x y:UnitType p n N) (z:BMark p n N)
    (d e:Rates)
    (X:Charts p n d) (V:Charts p n e)
    (c:PredictionClass) (g:PredictionData p d e r)
    (A B:Stalls p)
    (S:Straps (Label p.b)) (η ε β δ τ:ℝ)
    (hx:coordSpec z x X g.X)(hy:coordSpec z y V g.Y)
    (h:chorusClass p g U c τ)(hτ:0≤τ)(hl:2*τ<1)
    (ht:countStory p K η δ ε β U)
    (ha:reports p r U (wake p Y m x X) β δ)
    (hb:reports p r U (wake p Y m y V) β δ)
    (hs:g.colored U (wake p Y m x X) (wake p Y m y V) A B (2*ε))
    (hk:∀ i,d i≤K^2)(hq:∀ i,e i≤K^2)
    (hg:3≤p.g)(hμ:10*ε≤τ)
    (hA:seeking p A)(hB:seeking p B)
    (he:sizeB S 800)
    (T:Cross p n)
    (hF:glint p (z x)=glint p (z y))
    (hQ:c.compatible g.α (glint p (z x))
       (cardTone z x T,cardTone z y (reciprocal p T))) :
    let C:=stellar U (wake p Y m x X) (wake p Y m y V) η A B
    Guild.rich C→scorecard (chapter C S) (hailing p X V T) := by
  classical
  intro C hC
  by_contra hc
  obtain ⟨j,h1,h2,h3⟩:= jargon_score _ _ hc (rich_covers C hC S (fun i=>(he i).trans (by norm_num)))
  let L:= wake p Y m x X; let R:=wake p Y m y V
  let A':=outstraps A S true; let B':=outstraps B S false
  have hS:g.colored U L R A' B' (2*ε):= by
    exact ⟨fun i z hz=> hs.1 i z (mt (Finset.mem_union_left _) hz),
      fun i z hz=> hs.2 i z (mt (Finset.mem_union_left _) hz)⟩
  have hh i:= duet_edge g j i hg ht.h ha hb A' B' hS (outcard p A S hA he _ _)
    (outcard p B S hB he _ _) (counter_bill j ht ha hb _ _ S i h2 (hk _) (hq _)) ht.he
    (show 0 ≤ 2*ε from by linarith only [ht.he]) ht.hb (show 3*ε+2*ε<1/2*β from
      by linarith only [ht.high,ht.he])
  apply h3
  refine harmony g U c τ z x y T X V hx hy hg h ht.h.1 hF hQ j hτ hl h1
    (fun i=>⟨(hh i).1,(hh i).2.1⟩) (fun i=>⟨(hh i).2.2.1,(hh i).2.2.2.1⟩)
    (fun i l q=>((hh i).2.2.2.2 l q).trans (by linarith only [hμ]))

structure pilot (p:Shape) (d: Rates) (r:ℕ) where
  m : Bool→ Pulsar p r

structure hue (c:PredictionClass) (Y:Silhouette p N r) (f:Bool→ Pulsar p r)
    (u:Bool→Augur p N) (α:Party) (τ:ℝ) :Prop where
    consistent : c.lit α
    pulse_eq : c≠dusk → ∀ i,fromPulse Y (f i)=u i
    atDawn : c=dusk→∀ i,f i=0
    recording : c.recital p u α τ

theorem paintChorus (c:PredictionClass) (Y:Silhouette p N r) (f:Bool→ Pulsar p r)
    (u:Bool→Augur p N) (α:Party) (τ:ℝ)
    (h:hue c Y f u α τ) (A:styles d) (B:styles e) :
    chorusClass p (⟨α,f,A,B⟩:PredictionData p d e r) (wisp p Y) c τ := by
  classical
  refine ⟨h.consistent,?_,?_⟩
  · intro hg i j l k; change f i j l k=0; rw [h.atDawn hg]; rfl
  intro j hc ha hb x y
  obtain ⟨he,hf⟩:= ha (x,y)
  apply h.recording.2 x y (j.left y) (j.right x) (j.gam (x,y)) (he.symm.trans hf)
  intro l q
  specialize hb (x,y) l q
  unfold tabRef assembly; rw [← h.pulse_eq hc x,← h.pulse_eq hc y]
  unfold ChorusCost wisp at hb; rw [mapW_pr] at hb; exact hb

set_option maxHeartbeats 900000 in
theorem crew_praise (p:Shape) {q: PreparationParameters} (c:PredictionClass) (Y:Silhouette p N r)
    (f:Bool→ Pulsar p r) (u:Bool→Augur p N) (α:Party) (τ:ℝ) (h:hue c Y f u α τ)
    (m:Mixer p n)(A:Charts p n d)(g:styles d)(w:BMark p n N)
    (x:UnitType p n N) (H S : Stalls p) (hS:H ≤ S)(hp:coordSpec w x A g)
    {δ ε:ℝ} (he:0≤ε)(hd:δ≤ε) (ht:AnalyticParameters p M q s0)(hn:2*p.r≤n)
    (hf:claimed p x u m (w x) α H (scanPrice p*ε))
    (hg:c=dusk → exactInk p m w x) (hG:gauze p δ δ Y m q.pins x):
    ∀ i,praise (wisp p Y) (wake p Y m x A) i (S i) (yokeSet (g i) (α i)) (f i) (2*ε) := by
  classical
  intro i a ha hz
  let L:=S i
  have hk : postulates p (onSide x i) (fromPulse Y (f i)) (compass i x A m (g i) (α i))
      (H i) (scanPrice p*ε) := by
    unfold compass; rw [hp i]
    by_cases hC:c=dusk
    · have heq:= dusk_lit α (hC ▸ h.consistent)
      rw [heq,h.atDawn hC i]
      intro s hs z v
      have hj (y:Knobs p.g n): ¬mismatch p (fromPulse Y 0) (yoke p m x i (w x i) 1) z s v
        (onSide x i) y := by
        exact fun hk=>hk (show _= (0:F) from hg hC i _ (mem_useAtom ..))
      simp_rw [eq_false (hj _),pr_false]; exact mul_nonneg (scanPrice_pos _).le he
    rw [h.pulse_eq hC]; exact hf i
  have hi:= ht.enter.first
  exact (predict_praise A Y i x m (g i) (α i) (f i) (H i) he hi.hR hn
    (fun a h=> (hG i a).1 h) hk a (fun hx=>ha (hS i hx)) hz).trans
      (show ε+δ ≤ 2*ε from by linarith only [hd])

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
