import OAI.Combinatorics.HadwigerCounterexample.PositiveTestMass

namespace OAI

/-! # Aggregate Cost Bounds -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Filter Function
open scoped BigOperators Topology
open Template
variable {p:Shape} {n N r M s0 K:ℕ}
namespace StatusAnalysis
open PreparationParameters Station DualAnalysis

theorem couplings {I A : Type} [Fintype I] [Fintype A] (p:Wgt I)(f:I→ Wgt A)
    (F:(I×A)×(I×A)→ℝ):
    avg (pairW (semi p f) (semi p f)) F=
      avg (pairW p p) (fun i=>avg (pairW (f i.1) (f i.2)) (fun a=>F ((i.1,a.1),(i.2,a.2)))) := by
  rw [pairW_avg,pairW_avg]
  simp_rw [semi_avg,pairW_avg]
  refine avg_congr (fun i _=>?_); exact avg_avg ..

theorem ship_cost (w:LeafMixture p n N)(U:Wgt (UnitType p n N))(m:Mixer p n)
    (v:Station p n N K w) (i:Scrip p K) (Y:Silhouette p N r) :
    avg (cirque w U) (fun x=>v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2))
     = v.stratum i.2.2 m U i.2.1 Y := couplings (portionW U w.T) (fun i=>partW U i.val) _

theorem ship_pos (w:LeafMixture p n N) (m:Mixer p n)
    (v:Station p n N K w) (i:Scrip p K) (Y:Silhouette p N r)
    (h:i.2.2.permission)(hp:1≤p.r)(hn:2*p.r≤n)
    (x:ViewPair p n N w):
    0≤ v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2) := by
  classical
  let a:=i.2.2
  have hA j:= Appearance.witLaw (a.qA.allure_apt a.t a.z h.2.1 j) hp hn
  have hB j:= Appearance.witLaw (a.qB.allure_apt a.t a.z h.2.2.1 j) hp hn
  let s:= v.cAxes x.1.1 (toRates i.1.2.1)
  let t:= v.cAxes x.2.1 (toRates i.1.2.2)
  have hc (j) : 0≤ a.chimera x.1.2 x.2.2 s t m Y j := avg_nonneg (unifOn_sub _).nz
    (fun k=> mul_nonneg (a.qA.seraphFloor a.t a.z x.1.2 m s Y j (hA j) k).1
      (a.qB.seraphFloor a.t a.z x.2.2 m t Y j (hB j) k).1)
  have hM : 0≤a.momus:= mul_nonneg (kappa_pos _).le (kappa_pos _).le
  exact mul_nonneg (ind_nonneg _) (mul_nonneg hM (Finset.prod_nonneg fun i _=>hc i))

theorem prognosis (w:LeafMixture p n N) (U: Wgt (UnitType p n N)) (m:Mixer p n)
    (b:PreparationParameters) (v:Station p n N b.pins w) (Y:Silhouette p N r)
    {ε a : ℝ} (he:0 ≤ ε)(ha:0<a) (hp:1≤p.r)(hn:2*p.r≤n)
    (hs:Lead U w m b)
    (h:∀ i:Scrip p b.pins,i.2.2.permission→v.stratum i.2.2 m U i.2.1 Y ≤ ε):
    pr (cirque w U) (fun x=> eligiblePair v m x.1 x.2 Y a)≤ num (Scrip p b.pins)*(ε/a) := by
  classical
  let J:= Scrip p b.pins; let I:=ViewPair p n N w; let V:=cirque w U
  let Q (i:J)(x:I):= v.twilight i.2.2 m i.2.1 Y x.1.1 x.2.1 (x.1.2,x.2.2)
  have ht:= (troupe_bill hs).1; have hv:IsLaw V:=pairW_law ht ht
  let P (i:J)(x:I):= i.2.2.permission∧ a ≤ Q i x
  have hF (i:J): pr V (P i)≤ ε/a := by
    by_cases ht:i.2.2.permission
    · simp only [P,ht,true_and]
      refine (le_div_iff₀ ha).mpr ?_
      rw [mul_comm]
      exact ((le_avg_markov hv.nz (ship_pos w m v i Y ht hp hn) a).trans_eq (ship_cost ..)).trans
        (h i ht)
    rw [show P i=(fun _=>False) from funext fun a=>eq_false fun hh=>ht hh.1,pr_false]; exact div_nonneg he ha.le
  change pr V (fun x=>∃ i,P i x)≤ _
  exact ((pr_exists_le hv.nz P).trans (Finset.sum_le_sum fun i _=> hF i)).trans_eq (by simp [J,num])

structure Beams (b:PreparationParameters) (m:Mixer p n) (Y:Silhouette p N r)
    (w:LeafMixture p n N)(U:Wgt (UnitType p n N)) (v:Station p n N b.pins w)
    (a ε δ τ :ℝ):Prop where
   soft : origami p r (wisp p Y) δ
   rare : pr (w.sap U) (fun i=>¬gauze p δ δ Y m b.pins i) ≤ τ
   zone : pr (cirque w U) (fun x=> eligiblePair v m x.1 x.2 Y a) ≤ τ
   haze : 0<δ∧ δ≤ ε

variable {l:Filter ℕ} {m:cycleM p} {U:tale p M} {w:rhythms p M} {b:PreparationParameters}
set_option maxHeartbeats 1400000 in
theorem lightmap (v:Stations p M b.pins w) (h:veil p M b s0 l m w U)
    (a ε τ:ℝ) (ha:0<a)(he:0<ε)(hτ:0<τ)
    (k:ℕ)(Y:∀ n,Silhouette p (M*n) k):
    ∃ (r:ℕ) (δ:ℝ), ∀ᶠ n in l,
      ∃ X:Silhouette p (M*n) r,refines X (Y n)∧
        Beams b (m n) X (w n) (U n) (v n) a ε δ τ := by
  classical
  let L:= num (Scrip p b.pins); have hL:0≤L:=Nat.cast_nonneg _
  let η := a*τ/(L+1)
  have hη:0<η:=by unfold η; positivity
  let u:= min τ (min ε (1/4))
  have hu :0<u:=lt_min hτ (lt_min he (by norm_num))
  obtain ⟨r,δ,hd,hV,hT⟩:= lateSilk v h η u hη hu k
  refine ⟨r,δ,?_⟩; have he:= h.easel.enter.first
  filter_upwards [h.upright,hT,h.moment,h.durableS.shape,h.durableS.mass.positive,
    (trend_sizes l h.timeL he.hM).2.eventually (eventually_ge_atTop (2*num (Toast p)+1))]
    with n hn ht hp hC hP hN
  obtain ⟨X,hX,hW,hY⟩:=ht (Y n)
  let N:=M*n
  refine ⟨X,hX, ?_,hW.trans (min_le_left ..),?_, hd,?_⟩
  · have h0 i j:IsLaw (wisp p X i j):=
      mapW_law (omegaLaw p i j (show 2*num (Toast p)-(N:ℝ)≤-1 by
        change _≤(N:ℝ) at hN
        linarith only [hN])) _
    refine ⟨h0,fun i j=>?_⟩
    let ν:=wisp p X i j
    have hs : pr ν (fun i=>¬δ≤ν i) = 1-pr ν (fun i=>δ≤ν i) :=by rw [pr_not,(show tot ν=1
      from (h0 i j).total)]
    have hi:u≤1/4:=le_trans (min_le_right ..) (min_le_right ..)
    simp_rw [not_le] at hs
    have hf:= haze_small ν δ hd.le
    linarith only [hf,hs,hV,hi,hd]
  · apply (prognosis (w n) (U n) (m n) b (v n) X hη.le ha he.hR hn.age
      ⟨hC.1,hP,hp.1.law,hC.2⟩ hY).trans
    change L*(η/a)≤τ
    have h : η/a= τ/(L+1) := by unfold η; field_simp
    rw [h,mul_div_assoc',div_le_iff₀ (by linarith)]
    linarith only [hτ]
  have hi:u≤ε:=le_trans (min_le_right ..) (min_le_left ..)
  nlinarith only [hi,hV,hd,Nat.cast_nonneg (α:=ℝ) r]

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
