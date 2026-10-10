import OAI.Combinatorics.HadwigerCounterexample.CompatiblePairTests

namespace OAI

/-! # Final Contradiction -/

noncomputable section
namespace HadwigerCounterexample
open Filter Matrix Finset Module LinearMap Function
open scoped BigOperators Topology
open Template
namespace StatusAnalysis
open PreparationParameters Station PredictionClass Club Guild DualAnalysis
variable {p:Shape} {n N M r s0:ℕ} {w:rhythms p M}
    {m:cycleM p} {u:tale p M} {b:PreparationParameters} {l:Filter ℕ}

private theorem focused (x:Sketch p M):
    ∃ (L:ℕ) (Y:∀ n,Silhouette p (M*n) L),∀ (n r:ℕ) (X:Silhouette p (M*n) r),
      refines X (Y n) → ∀ τ:ℝ, recital x.c p (fun i=>x.g i n) x.α τ →
        ∃ f:Bool→ Pulsar p r,hue x.c X f (fun i=>x.g i n) x.α τ := by
  classical
  let L:=Fintype.card (Bool→ F); let E:=Fintype.equivFin (Bool→F)
  let Y (n:ℕ):Silhouette p (M*n) L := fun i q y=> E (fun j=> x.g j n i q y)
  refine ⟨L,Y,fun n r X h τ ht=>?_⟩
  choose f hf using h
  by_cases he : x.c=dusk
  · exact ⟨0,ht.1,fun hh=>(hh he).elim,fun _ _=>rfl,ht⟩
  let g j i q k:= (E.symm (f i q k)) j
  have hv j: fromPulse X (g j)=x.g j n:= by
    unfold fromPulse g; funext i q y; rw [← hf]
    exact congr_fun (Equiv.symm_apply_apply E _) j
  exact ⟨g, ht.1,fun _=>hv,fun h=>(he h).elim,ht⟩

private theorem haveLeads (h:veil p M b s0 l m w u) :
    ∀ᶠ n in l,Lead (u n) (w n) (m n) b:= by
  filter_upwards [h.durableS.shape,h.moment,h.durableS.mass.positive] with n hn ht hh
  exact ⟨hn.1,hh,ht.1.law,hn.2⟩

set_option maxHeartbeats 1400000 in
theorem goldEnd (v:Stations p M b.pins w) (h:veil p M b s0 l m w u) (ht:∀ᶠ n in l,(v n).bank)
    (hs:l.NeBot) (x:Sketch p M)
    (hb:b.bright l p M m w x) (hf:glowOutcome l p M u w x) : False := by
  classical
  obtain ⟨A,hA,hF⟩:=hf
  obtain ⟨τ,hτ,hT⟩:=hb.forecasts.classes
  let B:=min τ (1/4); have hB:0<B:=lt_min hτ (by norm_num)
  let K:= b.pins
  obtain ⟨ε,η,he,hM,hC⟩:= cheapFest p K (B/10) (by positivity)
  obtain ⟨a,hp⟩:= engagedBudget p K hC.pos
  obtain ⟨L,Y,hY⟩:=focused x
  obtain ⟨r,d,hr⟩:=lightmap v h a ε (A/4) hp.1 he (by positivity) L Y
  have heE:=h.easel
  have hX:∀ᶠ n in l,False := by
    filter_upwards [haveLeads h,h.upright,ht,hb.engraved,hT,hF,hr,hb.forecasts.small
      _ (show 0<scanPrice p*ε from mul_pos (scanPrice_pos _) he)]
      with n hn ht' h heq hf hξ hT hx_
    obtain ⟨X,hX,hP⟩:=hT
    have hh: recital x.c p (fun i=>x.g i n) x.α B := ⟨hf.1,fun i j s t r hi hg=>hf.2 i j s t r
      hi (fun i j=>(hg i j).trans (min_le_left ..))⟩
    obtain ⟨f,hf⟩:= hY _ _ X hX B hh
    let W:=KAspect (w n); let V:=cirque (w n) (u n)
    let H (i:W):=¬gauze p d d X (m n) K i.2
    let P (i:W×W):= eligiblePair (v n) (m n) i.1 i.2 X a
    let S := fun i:UnitType p n (M*n)×_=>matchProg x n i∧secureAt p (w n).rooting i
    let T:= fun i:W×W=> S (i.1.2,i.2.2)
    have hD i (hi: V i≠0)(hq:T i): ((H i.1∨H i.2) ∨ P i):=by
      by_cases hc:H i.1∨ H i.2
      · exact Or.inl hc
      refine Or.inr (foretold w m x _ h _ hn heE heq ht'.age X f hf he hC hp hx_
        (show 10*ε≤B from by linarith only [hM])
        (show 2*B<1 by have h: B≤1/4:=min_le_right ..; linarith only [h])
        hP i hi (not_not.mp (mt Or.inl hc)) (not_not.mp (mt Or.inr hc)) hq.1 hq.2)
    have hQ0 := (troupe_bill hn).1; have hV:IsLaw V:=pairW_law hQ0 hQ0
    have hV' : pr V T ≥ A := by
      unfold gilded at hξ; rw [←cirque_unit _ hn,mapW_pr] at hξ; exact hξ
    have h1 := (sickBound (u n) (v n) X hn _ _ _ _ hP).2
    have h2 : pr V T ≤ (A/4+A/4)+A/4:= ((pr_on_mono hV.nz hD).trans
      (pr_or_le hV.nz)).trans (add_le_add h1 hP.zone)
    linarith only [h1,h2,hV',hA]
  exact hX.exists.elim (fun _ h=>h)

set_option maxHeartbeats 1200000 in
theorem quietEnd (v:Stations p M b.pins w) (h:veil p M b s0 l m w u)
    (ht:∀ᶠ n in l,(v n).bank) (hs:l.NeBot)
    (hq:b.silenceOutcome l p M m u w) : False := by
  classical
  obtain ⟨τ,hτ,hQ⟩:=hq
  let K:=b.pins
  obtain ⟨ε,η,he,hM,hC⟩:= cheapFest p K (τ/20) (by positivity)
  obtain ⟨a,hp⟩:= engagedBudget p K hC.pos
  obtain ⟨r,d,hr⟩:=lightmap v h a ε (1/16) hp.1 he (by norm_num) 1
    (fun _ _ _ _=>0)
  have hF:∀ᶠ n in l, False := by
    filter_upwards [hr,hQ,ht,h.upright,haveLeads h] with n hn hq ht hi hx
    obtain ⟨X,_,hE⟩:=hn
    exact no_out (w n) b (m n) X (u n) _ _ _ _ _ τ hx ht h.easel hi.age hC he hp hE
      (by linarith only [hM]) hq.1 hq.2
  exact hF.exists.elim (fun _ hi=>hi)

instance stationInhabited (p : Shape) (n N K : ℕ) (w:LeafMixture p n N) :
    Inhabited (Station p n N K w) := ⟨⟨fun _ _ _=>0,fun _ _ _=>0⟩⟩

theorem refuteVeil (h:veil p M b s0 l m w u) (hs:l.NeBot)
    (hT: b.silenceOutcome l p M m u w ∨ b.predOutcome l p M m u w) :
    False := by
  classical
  have he :
      ∀ᶠ n in l, ∃ s:Station p n (M*n) b.pins (w n),s.bank := by
    filter_upwards [h.durableS.shape] with n hn
    exact Station.create (fun x=>(hn.1.leaf _ x.property).bound)
  obtain ⟨s,hq⟩:= taking he
  rcases hT with hP|⟨b,hf,hR|hR⟩
  · exact quietEnd s h hq hs hP
  · exact goldEnd s h hq hs b hf hR
  exact dim_end h s hq hs b hf hR
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
