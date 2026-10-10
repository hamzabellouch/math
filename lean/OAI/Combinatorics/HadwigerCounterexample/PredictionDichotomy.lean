import OAI.Combinatorics.HadwigerCounterexample.PreliminaryRestrictions

namespace OAI

/-! # Prediction Dichotomy -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {U : Ultrafilter ℕ} {P : Campaign p M}

def outlook (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) :=
  ∃ ε:ℕ→ℝ, slight l ε ∧ ∀ᶠ n in l,q.predicts p (M*n) (m n) (s n) (w n) (ε n)

theorem eclipse (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    q.silenceOutcome (U:Filter ℕ) p M m w s ∨ q.outlook (U:Filter ℕ) p M m w s := by
  classical
  let P (n : ℕ) ε := q.predicts p (M*n) (m n) (s n) (w n) ε
  let c (i:ℕ) := ((i:ℝ)+1)⁻¹
  by_cases he : ∀ k : ℕ,∀ᶠ n in U,P n (c k)
  · obtain ⟨k,h1,h2⟩:= diagonal_gains (U:Filter ℕ) hl (fun i j=>P i (c j)) he
    exact Or.inr ⟨fun i=>c (k i),slight_inv_stage h1,h2⟩
  push Not at he
  obtain ⟨k,hk⟩:=he
  exact Or.inl ⟨c k, by unfold c; positivity,
    hk.and (((retainInitial hl hq hx).unconditional hl hq hw).mono fun i hi=>hi.2)⟩

structure Sage (p : Shape) (n N : ℕ) where
  g : Bool→Augur p N
  m : BMark p n N
  L : UnitType p n N → Bool→ Finset (Label p.b)

instance : Inhabited (Sage p n N) := ⟨⟨fun _ _ _ _=>0,fun _=>0,fun _ _=>∅⟩⟩

abbrev Banners := Party × F × Bool

def tender {p : Shape} {n N} (i : Sage p n N) (q : PreparationParameters) (m : Mixer p n)
    (s : LeafMixture p n N) (z : Banners) (ε : ℝ) (x : UnitType p n N) :=
  q.seems p m s x i.g (i.m x) (i.L x) z.1 ε ∧ glint p (i.m x)=z.2.1 ∧
    ((z.2.2=true) ↔ delta i.m x=0)

def crowdSeed : ℝ := 2*pollen
theorem crowdSeed_pos : 0<crowdSeed := mul_pos (by norm_num) pollen_pos

set_option maxHeartbeats 1200000 in
theorem cohort (m : Mixer p n) (w : Wgt (UnitType p n N)) (s : LeafMixture p n N)
    (hs : q.entered p N m w s) (hw : IsLaw w) {ε : ℝ}
    (h : q.predicts p N m s w ε) :
    ∃ (z : Banners) (i : Sage p n N), (∀ x j,totalRank (i.m x j)≤q.e) ∧
      crowdSeed ≤ pr (s.sap w) (tender i q m s z ε) := by
  classical
  let v:=s.sap w
  have hv := LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) hs.weight) hw
  obtain ⟨g,hg⟩:=h
  let P (x : UnitType p n N) := ∃ z L α, q.seems p m s x g z L α ε
  let Q x:= v x≠ 0∧P x
  have ht : pr v Q=pr v P := avg_congr fun x h=> (by change ind (v x≠0∧P x)=ind (P x); rw [show (v x≠0∧P x)=(P x) from propext (and_iff_right h)])
  choose f hf using show
    ∀ x : UnitType p n N,∃ (z : Bool→Profile p n) (L : Bool→Finset (Label p.b))
      (α : Party), (∀ j,totalRank (z j)≤ q.e) ∧ (Q x → q.seems p m s x g z L α ε) from by
    intro x; by_cases h : Q x
    · obtain ⟨z,L,a,hv⟩:=h.2
      refine ⟨z,L,a,fun i=>?_,fun _=>hv⟩
      exact (effective_rank (hv.1 i).2).trans (LeafMixture.root_bound hs.strength _)
    refine ⟨0,fun _=>∅,0,fun i=>?_,fun he=>(h he).elim⟩
    unfold totalRank
    have hh (j:Comp p.g) :
        ((0:Profile p n) j).rank=0 := Matrix.rank_zero
    exact le_trans (Finset.sum_eq_zero (fun i _=>hh i)).le (Nat.zero_le _)
  choose L a hA hh using hf
  let i:= (⟨g,f,L⟩: Sage p n N)
  have he x (h : Q x) : ∃ z : Banners,tender i q m s z ε x := by
    refine ⟨(a x,glint p (i.m x),decide (delta i.m x=0)),hh x h,rfl,?_⟩
    simp
  have ht' : (0.000001:ℝ) ≤ ∑ j : Banners,pr v (tender i q m s j ε) :=
    hg.trans ((ht.symm ▸ pr_mono hv.nz he).trans (pr_exists_le hv.nz _))
  have hz : ∃ j : Banners,crowdSeed ≤ pr v (tender i q m s j ε) := by
    by_contra! h
    have hx : 0.000001≤∑ _j : Banners,crowdSeed :=
      ht'.trans (Finset.sum_le_sum fun j _=>(h j).le)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hx
    simp [Banners,Party,F,Vec,ZMod.card] at hx
    norm_num [crowdSeed,pollen] at hx
  obtain ⟨j,hj⟩:=hz
  exact ⟨j,i,hA,hj⟩

set_option maxHeartbeats 1800000 in
theorem pruneWhisper (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (hc : b.c=dusk)
    (hf : ledger b (U:Filter ℕ))
    (hg : ∀ i,∃ r, disappearing U (b.g i) r)
    (h : ∀ᶠ n in U, crowdSeed ≤ pr ((s n).sap (w n)) (P n) ∧
       ∀ x,P n x → q.seems p (m n) (s n) x (fun i=>b.g i n) (b.m n x) (b.L n x) b.α (b.ε n)) :
    ∃ Q:Campaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→P n x∧exactInk p (m n) (b.m n) x := by
  classical
  have ha : ∀ i,b.α i=1 := dusk_lit _ (hc ▸ hf.light)
  choose g hG using hg
  let Y (n) (x : UnitType p n (M*n)) i := whisper p (b.g i n) (g i) (onSide x i)
  let Q : Campaign p M := fun n x=>P n x∧∀ i,Y n x i
  have he :
      ∀ᶠ n in U,∀ (i : Bool) (l : Tag p.g) (b':F),tabRef p l b' (b.g i n) (g i) ≤1/100 :=
    eventually_all.mpr fun i=> eventually_all.mpr fun l=> eventually_all.mpr fun b'=> hG i l b'
      _ (by norm_num)
  have hz :
      ∀ᶠ n : ℕ in atTop, (2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))≤pollen := by
    have hh : Tendsto (fun n:ℕ=>(2:ℝ)*(2*q.L*bp (-(1/16:ℝ)*n))) atTop (𝓝 0) := by
      have h := ((bp_nat_vanish (by norm_num : 0<(1/16:ℝ))).const_mul (2*q.L)).const_mul 2
      simpa using h
    exact (hh.eventually (gt_mem_nhds pollen_pos)).mono (fun _ hi=>hi.le)
  refine ⟨Q,?_⟩
  filter_upwards [hw,hx,h,hq.wrap.filter_mono hl,he,hf.small (1/16) (by norm_num),
    (hushCalendar p M hq.hM hq.hG hq.hR hq.hJ).filter_mono hl,hz.filter_mono hl,
    (eventually_ge_atTop (2*p.r)).filter_mono hl] with n hn ht hs hq' hG hε hh hz hN
  let s':=s n; let w':=w n
  let v:=s'.sap w'
  have hv : IsLaw v:= LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) ht.weight) hn.law
  have hS : bySide p v (m n) (2*q.L) := by
    refine LeafMixture.upperSide hn.border (K':=2) (fun x=>?_) (by norm_num) le_rfl
    exact (on_mon hn.law.nz (by norm_num) ht.weight x).trans_eq (by norm_num)
  constructor
  · let V (x : UnitType p n (M*n)) := ∀ i,Y n x i
    have hT := pr_shield hv.nz (P n) V
    let δ := 2*q.L*bp (-(1/16:ℝ)*n)
    have hi (i:Bool) : pr v (fun x=>¬Y n x i) ≤ δ := by
      let T (o:Orient p n (M*n)) := ¬ whisper p (b.g i n) (g i) o
      let f x:= onSide (x:UnitType p n (M*n)) i
      change pr v (fun x=>T (f x)) ≤ _
      rw [←mapW_pr]
      apply (pr_cap (hS i) T).trans
      exact mul_le_mul_of_nonneg_left (hh (m n) hq'.1 _ _ (hG i))
        (mul_nonneg (by norm_num) hq.early.hL)
    have hf : pr v (fun x=>¬V x)≤pollen := by
      refine le_trans ?_ hz
      calc pr v (fun x=>¬V x)
        _ ≤ ∑ i:Bool,pr v (fun x=>¬Y n x i) :=
          (pr_mono hv.nz (p:=fun x=>¬V x) (fun x h => show ∃ i:Bool,¬Y n x i from not_forall.mp h)).trans
            (pr_exists_le hv.nz _)
        _ ≤ 2*δ := by rw [Fintype.sum_bool,two_mul]; exact add_le_add (hi _) (hi _)
    have hh : 2*pollen ≤ pr v (P n) := hs.1
    exact le_trans (by linarith only [hh,hf]) hT
  · intro x hh
    have hs := hs.2 x hh.1
    refine ⟨hh.1,fun i=>?_⟩
    have hi :
        postulates p (onSide x i) (b.g i n) (yoke p (m n) x i (b.m n x i) 1) (b.L n x i) (1/16) := by
      rw [←ha i]
      exact fun z hz j k=>(hs.2 i z hz j k).trans hε
    have he : (↑(b.L n x i).card:ℝ)<bp ((p.b:ℝ)-2*p.j) :=
      lt_of_le_of_lt (by exact_mod_cast (hs.1 i).1) hq.hB
    exact (hush_vat _ _ _ _ (g i) he hi (hh.2 i) hq.hg hq.hR hN).2

set_option maxHeartbeats 1600000 in
theorem outlook_to_dose (hl : (U:Filter ℕ)≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n))
    (h : q.outlook (U:Filter ℕ) p M m w s) :
    ∃ (b : Sketch p M) (P : Campaign p M) (i : Bool), q.dosed (U:Filter ℕ) p M m w s b P ∧
       ∀ᶠ n in U, ∀ x,P n x → ((i=true) ↔ delta (b.m n) x=0) := by
  classical
  obtain ⟨ε,hε,h⟩:=h
  let R (n : ℕ) (z : Banners) (i : Sage p n (M*n)) :=
    (∀ x j,totalRank (i.m x j)≤q.e) ∧ crowdSeed≤pr ((s n).sap (w n)) (tender i q (m n) (s n) z (ε n))
  have hh : ∀ᶠ n in U,∃ (z:Banners) (i:Sage p n (M*n)),R n z i := by
    filter_upwards [h,hw,hx] with n hn ht hv
    exact cohort (m n) (w n) (s n) hv ht.law hn
  obtain ⟨z,hz⟩ := Ultrafilter.eventually_exists_iff.mp hh
  obtain ⟨i,hi⟩ := taking hz
  let g (j:Bool): season p M := fun n => (i n).g j
  obtain ⟨c,τ,hτ,hG,hL,hB⟩:= examine U p M g z.1
  let b:= (⟨c,z.1,z.2.1,fun n=>(i n).m,fun n=>(i n).L,g,ε⟩: Sketch p M)
  let P : Campaign p M := fun n => tender (i n) q (m n) (s n) z (ε n)
  have hT : ledger b (U:Filter ℕ):= ⟨hε,⟨τ,hτ,hG⟩,hL⟩
  have hk :
      ∃ Q : Campaign p M,∀ᶠ n in U, pollen ≤ pr ((s n).sap (w n)) (Q n) ∧
       ∀ x,Q n x→ P n x∧ (b.c=dusk→exactInk p (m n) (b.m n) x) := by
    by_cases hC : c=dusk
    · obtain ⟨Q,hQ⟩:= pruneWhisper hl hq hw hx (show b.c=dusk from hC) hT (hB hC)
       (P:=P) (hi.mono fun n hn=>⟨hn.2,fun x h=>h.1⟩)
      exact ⟨Q,hQ.mono (fun n hn=>⟨hn.1,fun i h=>⟨(hn.2 i h).1,fun _=>(hn.2 i h).2⟩⟩)⟩
    exact ⟨P,hi.mono (fun n hn=>⟨le_trans (show pollen≤crowdSeed from
      by unfold crowdSeed; linarith only [pollen_pos]) hn.2,fun x h=>⟨h,fun hh=>(hC hh).elim⟩⟩)⟩
  obtain ⟨Q,hQ⟩:=hk
  have hB : ∀ᶠ n in U,pollen ≤ pr ((s n).sap (w n)) (Q n) := hQ.mono fun i hi=>hi.1
  have hc : q.citable (U:Filter ℕ) p M m w s b Q := by
    refine ⟨(warm.const (trend_sizes (U:Filter ℕ) hl hq.hM).2 pollen_pos).mono hB,hT,?_⟩
    filter_upwards [hQ] with n hn
    intro i hi x hx hp
    obtain ⟨⟨hr,hv,_⟩,hs⟩:= hn.2 x hp
    exact ⟨hr,hv,hs⟩
  refine ⟨b,Q,z.2.2,⟨hc,hB,hi.mono (fun i hi=>hi.1)⟩, hQ.mono fun i hi x hx=>?_⟩
  exact ((hi.2 x hx).1).2.2

set_option maxHeartbeats 1000000 in
theorem prepare (U : Ultrafilter ℕ) (hl : (U:Filter ℕ) ≤ atTop) (hq : q.planted p M)
    {s : rhythms p M} (hw : ∀ᶠ n in U,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in U,q.entered p (M*n) (m n) (w n) (s n)) :
    satisfied q (U:Filter ℕ) p M m w := by
  classical
  rcases eclipse hl hq hw hx with hn|hn
  · exact ⟨s,retainInitial hl hq hx,Or.inl hn⟩
  obtain ⟨b,P,i,hQ,hz⟩:= outlook_to_dose hl hq hw hx hn
  cases i
  · obtain ⟨R,hR,hT⟩:= phaseSplit hl hq hw hx hQ
     (hz.mono fun n hn i hi x h hh ht=> Bool.false_ne_true ((hn x hh).mpr ht))
    rcases Ultrafilter.eventually_or.mp hT with hF|hF
    · exact outByMix hl hq hw hx hR hF
    exact outByCover hl hq hw hx hR hF
  exact phaseAbsent hl hq hw hx hQ (hz.mono fun n hn i hi x h hh=>(hn x hh).mp rfl)
end PreparationParameters
end HadwigerCounterexample

end

end OAI
