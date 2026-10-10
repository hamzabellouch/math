import OAI.Combinatorics.HadwigerCounterexample.AggregateCostBounds

namespace OAI

/-! # Finite Comparison Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Finset Module LinearMap Filter
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M r s0:ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass DualAnalysis Club Guild

def trimBeta (p : Shape) (K:ℕ):=basebeta p K/2
theorem trimBeta_pos (p:Shape) (K:ℕ): 0<trimBeta p K:=half_pos (basebeta_pos _ _)

structure Jubilee (p : Shape) (K:ℕ) (ε η:ℝ) : Prop where
  pos : 0<η
  book : playbook p K*η≤ε
  sturdyR : playbook p K*η<1/2*trimBeta p K^2
  low : 6*ε<1/2*trimBeta p K
theorem cheapFest (p : Shape) (K:ℕ) (a:ℝ) (h:0<a) :
    ∃ ε η:ℝ,0<ε∧ε≤a∧Jubilee p K ε η := by
  let β:=trimBeta p K; have hβ:0<β:=trimBeta_pos p K
  let ε:= min a (min (β/14) (β^2/4)); let y:= playbook p K
  have hy:0<y:=playbook_pos _ _
  have he:0<ε:=lt_min h (lt_min (by positivity) (by positivity))
  have hF:=show ε≤β^2/4 from le_trans (min_le_right ..) (min_le_right ..)
  have hz:y*(ε/y)=ε:=by field_simp
  refine ⟨ε,ε/y,he,min_le_left ..,⟨div_pos he hy,hz.le,hz.trans_lt (hF.trans_lt ?_),?_⟩⟩
  · change β^2/4<1/2*β^2; nlinarith only [hβ]
  have hh:ε≤β/14:=le_trans (min_le_right ..) (min_le_left ..)
  change _<1/2*β; linarith only [hβ,hh]

variable {b:PreparationParameters}
theorem boothseek (q:PreparationParameters) (s:Plan p n) (p0 X:Stalls p)
    (h:booths p q.pins s p0) (hq:AnalyticParameters p M q s0) (hh:∀ i,(X i).card≤q.B):
    seeking p (p0⊔X) := by
  intro i
  have hf : ((p0⊔X:Stalls p) i).card≤(p0 i).card+(X i).card:= card_union_le ..
  have hi:= h.1 i; have he:= hh i; have hx:= hq.forbid; have hh:= hq.spare
  omega

theorem outcard (p:Shape) (s:Stalls p) (S : Straps (Label p.b))
    (h:seeking p s) (hs:sizeB S 800) (i j:Bool) :
    (outstraps s S i j).card < Fintype.card (Label p.b):= by
  apply lt_of_le_of_lt (card_union_le ..)
  have hv:=h j; have hg:= hs i; omega

variable {w:LeafMixture p n N} {m:Mixer p n}
theorem sickBound (U:Wgt (UnitType p n N)) (v:Station p n N b.pins w) (Y:Silhouette p N r)
    (h: Lead U w m b) (a ε δ τ:ℝ)
    (hp:Beams b m Y w U v a ε δ τ) :
    let P (i : Aspect p n N w):=¬gauze p δ δ Y m b.pins i.2
    pr (troupe w U) P ≤ τ ∧ pr (cirque w U) (fun x=> P x.1∨P x.2) ≤ τ+τ := by
  classical
  intro P
  let μ:=troupe w U; have hi:= (troupe_bill h)
  have hh :pr μ P ≤ τ := ((mapW_pr μ Prod.snd (fun i=>¬gauze p δ δ Y m b.pins i)).symm).trans_le
    (hi.2.symm ▸ hp.rare)
  refine ⟨hh,?_⟩
  apply (pr_or_le (pairW_law hi.1 hi.1).nz).trans
  refine add_le_add ?_ ?_
  · refine le_trans ?_ hh
    have h:= pairW_pr μ μ P (fun _=>True)
    have hl : IsLaw μ:=hi.1
    exact le_of_eq (by simpa [hl.total] using h)
  refine le_trans ?_ hh
  have h:=pairW_pr μ μ (fun _=> True) P
  have hl:IsLaw μ:=hi.1
  exact le_of_eq (by simpa [hl.total] using h)

structure Loupe (p : Shape) (n N K : ℕ) (s:LeafMixture p n N) where
   r : s.T → Stakes K
   H : s.T → Stalls p

structure Shipped (w:LeafMixture p n N) (K:ℕ) (u:Station p n N K w) (t:Loupe p n N K w) : Prop where
   charts i: charted (u.cAxes i (toRates (t.r i))) (w.pin i.val).sp
   baseline i: booths p K (w.pin i.val).sp (t.H i)

theorem ready_loupe (w:LeafMixture p n N) (u:Station p n N b.pins w) (hu:u.bank)
    (h:AnalyticParameters p M b s0) (he:∀ i:w.T,planRank (w.pin i.val).sp ≤ b.pins) :
    ∃ t,Shipped w b.pins u t := by
  classical
  choose d hd using fun i:w.T=>sizedCharts _ _ _ hu i (he i)
  choose S hS using fun i:w.T=> buildBooths _ _ (he i) h.penRoom
  exact ⟨⟨d,S⟩,hd,hS⟩
variable (w:LeafMixture p n N) (L:Loupe p n N b.pins w) (t:Station p n N b.pins w)
def routeC {K} (w:LeafMixture p n N) (L:Loupe p n N K w) (t:Station p n N K w)
    (x:Aspect p n N w) :=
   t.cAxes x.1 (toRates (L.r x.1))
abbrev KAspect {p:Shape} {n N:ℕ} (w:LeafMixture p n N):=Aspect p n N w

set_option maxHeartbeats 800000 in
theorem routeLive (h:Shipped w b.pins t L) (m:Mixer p n)
    (H: AnalyticParameters p M b s0) (hn:2*p.r≤n)
    (x:Aspect p n N w) (Y: Silhouette p N r)
    (δ:ℝ)(he:0<δ) (hk:planRank (w.pin x.1.val).sp ≤b.pins)
    (hp:gauze p δ δ Y m b.pins x.2) :
    reports p r (wisp p Y) (wake p Y m x.2 (routeC w L t x)) (trimBeta p b.pins) δ := by
  apply plume_reports p b.pins m Y (w.pin x.1.val).sp _ _ (h.charts x.1)
    _ hk H.enter.first.hG H.enter.first.hR hn δ he hp
  intro i; exact Nat.lt_succ_iff.mp (L.r x.1 i).isLt
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
