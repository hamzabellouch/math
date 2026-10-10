import OAI.Combinatorics.HadwigerCounterexample.PredictionExtraction

namespace OAI

/-! # Positive Test Mass -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Function Filter Finset LinearMap Module
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N K M s0 r :ℕ}
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {q:PreparationParameters} {w:LeafMixture p n N}

abbrev Aspect (p:Shape) (n N :ℕ) (w:LeafMixture p n N) := w.T × UnitType p n N
abbrev ViewPair (p:Shape) (n N :ℕ) (w:LeafMixture p n N) := Aspect p n N w × Aspect p n N w

def troupe (w:LeafMixture p n N) (U:Wgt (UnitType p n N)) :=
    semi (portionW U w.T) (fun i=>partW U i.val)
def cirque (w:LeafMixture p n N) (U:Wgt (UnitType p n N)) :=
   pairW (troupe w U) (troupe w U)
def eligiblePair (v:Station p n N K w) (m:Mixer p n) (i j:Aspect p n N w)
    (Y:Silhouette p N r) (a:ℝ) :=
   ∃ k:Scrip p K, k.2.2.permission ∧ a ≤ v.twilight k.2.2 m k.2.1 Y i.1 j.1 (i.2,j.2)

def supportBudget (p:Shape) (K:ℕ) (η a:ℝ) :=
   0<a ∧ ∀ k:Scrip p K,a ≤ k.2.2.momus* η^Fintype.card (Messenger (toFormat k.1.1))

theorem engagedBudget (p:Shape) (K:ℕ) {η:ℝ} (h:0<η) :
    ∃ a,supportBudget p K η a := by
  classical
  let F (i:Scrip p K) := i.2.2.momus*η^Fintype.card (Messenger (toFormat i.1.1))
  have hf i:0<F i := mul_pos (mul_pos (kappa_pos _) (kappa_pos _)) (pow_pos h _)
  cases isEmpty_or_nonempty (Scrip p K)
  next h => exact ⟨1,zero_lt_one,fun i=>(h.false i).elim⟩
  next h =>
    let g:=univ.image F
    have he:g.Nonempty:=image_nonempty.mpr univ_nonempty
    refine ⟨g.min' he, ?_,fun i=> min'_le _ _ (mem_image_of_mem _ (mem_univ _))⟩
    obtain ⟨i,hi,h⟩:=mem_image.mp (min'_mem _ he)
    exact h ▸ hf i

set_option maxHeartbeats 1400000 in
theorem inform (w:LeafMixture p n N) (v:Station p n N K w)
    (m:Mixer p n) (Y:Silhouette p N r) (i j:Aspect p n N w)
    (hc:PreparationParameters.frameSide p m i.2) (he:PreparationParameters.frameSide p m j.2)
    (ha:(w.pin i.1.val).agree i.2) (hb:(w.pin j.1.val).agree j.2)
    (d e:Stakes K)
    (h1:charted (v.cAxes i.1 (toRates d)) (w.pin i.1.val).sp)
    (h2:charted (v.cAxes j.1 (toRates e)) (w.pin j.1.val).sp)
    {η a:ℝ} (h : supportBudget p K η a)
    (x y:Stalls p) (hx:booths p K (w.pin i.1.val).sp x)
    (hy:booths p K (w.pin j.1.val).sp y)
    (P Q:Stalls p) (hF:x≤P)(hG:y≤Q)
    (hg:3≤p.g)(hp:1≤p.J)(hη:0<η)
    (k:Fin (2^deckMax p K))
    (hk:berthTicket (w.pin i.1.val) (w.pin j.1.val) (v.mails i.1 j.1 k) (i.2,j.2))
    (S:Straps (Label p.b)) :
    let X:= v.cAxes i.1 (toRates d); let W:=v.cAxes j.1 (toRates e)
    let C:=stellar (wisp p Y) (wake p Y m i.2 X) (wake p Y m j.2 W) η P Q
    (∀ i:Grid,(C i).travels S 100 (view _ _) (chapter C S i)) →
    scorecard (chapter C S) (hailing p X W (v.mails i.1 j.1 k)) →
    eligiblePair v m i j Y a := by
  classical
  intro X W C hA hB
  obtain ⟨q,g,F,G,hT,hU⟩:=processions p K P Q _ _ X W (v.mails i.1 j.1 k) h1 h2 hk.1 hk.2.1 x y hx hy
    hF hG (by omega) hp S hA hB
  let z:=g.binding p F G
  let I:Scrip p K:=⟨(q,d,e),k,z⟩
  refine ⟨I,hT.1,?_⟩
  obtain ⟨hL,hR⟩:= berth_flags _ _ _ hk ha hb
  have hC :
      v.frontPage z m i.1 j.1 k i.2∧v.backPage z m i.1 j.1 k j.2 :=
    ⟨⟨hT,ha,hc,hL⟩,⟨hT,hb,he,hR⟩⟩
  change _≤ ind _ * z.constellation i.2 j.2 X W m Y
  rw [ind_one hC,one_mul]
  refine (h.2 I).trans (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (kappa_pos _).le (kappa_pos _).le))
  let J:=Messenger (toFormat q)
  have hi (x:J):η ≤ z.chimera i.2 j.2 X W m Y x := (hU x).trans_eq
    (Engagement.solicit ..).symm
  exact le_trans (le_of_eq (show η^Fintype.card J=∏ _:J,η by simp)) (Finset.prod_le_prod₀
    (fun i _=> hη.le) fun i _=> hi i)

variable {U : Wgt (UnitType p n N)} {m : Mixer p n}

structure Lead (U: Wgt (UnitType p n N)) (w : LeafMixture p n N) (m:Mixer p n) (q:PreparationParameters) : Prop where
  strength : w.strength U (usual p m N) q.leafNew (2*q.ζ) q.pins
  amount : 0<w.amount U
  law : IsLaw U
  coverC : w.within (frameSide p m)

theorem troupe_bill (h:Lead U w m q) :
    IsLaw (troupe w U) ∧ mapW (troupe w U) Prod.snd=w.sap U := by
  classical
  obtain ⟨h1,h2⟩:=rebuild h.law.nz h.strength.part
    (fun i hi=>(h.strength.leaf _ hi).pos) h.amount
  have hk i:IsLaw (partW U (Subtype.val (show w.T from i))):=on_law h.law.nz (h.strength.leaf _
    i.property).pos
  constructor
  · constructor
    · intro x; exact mul_nonneg (h1.nz _) ((hk _).nz _)
    unfold troupe; rw [semi_total]; simp_rw [(hk _).total]; exact h1.avg_const _
  change _=allW U w.T; rw [h2]; funext i
  unfold mapW mixW pr troupe; rw [semi_avg]
  simp_rw [show ∀ w':↥w.T,avg (partW U w'.val) (fun x=> ind (x=i))=partW U w'.val i from
    (fun w=> pr_point' ..)]

theorem troupe_home (h:Lead U w m q) (x: Aspect p n N w) (hx:troupe w U x≠0):
    x.2∈x.1.val∧w.rooting x.2=(w.pin x.1.val).sp∧frameSide p m x.2∧ (w.pin x.1.val).agree x.2 := by
  have he : x.2∈x.1.val := (onW_ne (right_ne_zero_of_mul hx)).1
  exact ⟨he, congrArg Pin.sp (LeafMixture.poller_eq w h.strength.part x.1.property he),h.coverC _
    x.1.property x.2 he,(h.strength.leaf _ x.1.property).fixpin x.2 he⟩
theorem cirque_unit (w:LeafMixture p n N) (h: Lead U w m q) :
    mapW (cirque w U) (fun i=>(i.1.2,i.2.2)) = pairW (w.sap U) (w.sap U) := by
  classical
  have hk:=map_pair_law (troupe w U) (troupe w U) Prod.snd Prod.snd
  rw [(troupe_bill h).2] at hk; exact hk
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
