import OAI.Combinatorics.HadwigerCounterexample.PreparedOutcomes

namespace OAI

/-! # Prepared Population Trimming -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M} {b : Sketch p M}

theorem retainInitial (hl : l≤atTop) (hq : q.planted p M)
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    durable q l p M m w s := by
  refine ⟨((warm.const (trend_sizes l hl hq.hM).2 (by norm_num : 0<(1/2:ℝ))).mono
    (hx.mono fun i hi=> hi.weight)),?_⟩
  filter_upwards [hx] with n hn
  have hh := hq.early
  refine ⟨hn.strength.slide ?_ ?_ ?_ (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),
    fun i hi x hx => (hn.onTile i hi x hx).2.2.2⟩
  · unfold leafNew; linarith [(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s :
      0≤(q.s:ℝ))]
  · linarith only [hh.pos]
  unfold pins; omega

abbrev Campaign (p : Shape) (M : ℕ) := ∀ n,UnitType p n (M*n) → Prop
variable {P : Campaign p M}
structure citable (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) (b : Sketch p M) (P : Campaign p M) : Prop where
  mass : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>pr ((s i).sap (w i)) (P i))
  forecast : ledger b l
  mark : ∀ᶠ i in l, (s i).within (fun x => P i x → engrave b q m s i x)

def potion (s : rhythms p M) (w : tale p M) (P : Campaign p M) : tale p M :=
  fun n => onW ((s n).sap (w n)) (P n)
def charm (s : rhythms p M) (w : tale p M) (P : Campaign p M) (b : Sketch p M) :=
  fun n => pr (pairW (potion s w P n) (potion s w P n)) (matchProg b n)

theorem citable.on_law (h : citable q l p M m w s b P)
    (hl : l ≤ atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    ∀ᶠ n in l, IsLaw (potion s w P n) := by
  filter_upwards [h.mass.positive,hw,(retainInitial hl hq hx).mass.positive] with n hn ht hv
  exact HadwigerCounterexample.on_law (LeafMixture.sapLaw hv ht.law).nz hn

set_option maxHeartbeats 1400000 in
theorem dropHarvest (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P) :
    ∃ t : rhythms p M, durable q l p M m w t ∧
      q.bright l p M m t b ∧
      (∀ᶠ n in l,(t n).within (fun x=>inTiles (s n).T x∧P n x)) ∧
      ∃ d,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) d ∧
        ∀ᶠ n in l,charm s w P b n-d n ≤ glow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z n:=((N n):ℝ)
  let Y : Campaign p M := fun n=> inTiles (s n).T
  let E :=fun i=> bp (-q.ζ*z i)
  let R n (t : LeafMixture p n (M*n)) := t.strength (w n) (usual p (m n) (M*n)) (q.leafOld+q.ζ) (2*q.ζ) q.e ∧
    LeafMixture.elder (s n) t (P n) (fun i j=> t.pin i=(s n).pin j) ∧
    pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n
  obtain ⟨t,ht⟩ : ∃ t: rhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx] with n hn h
    exact LeafMixture.elder_trim h.strength hq.early.pos.le hn.law _
  have hz := (trend_sizes l hl hq.hM).2
  let Q : Campaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := fun h=>⟨fun x hx=>LeafMixture.ancestral h.2.1 hx,h.2.2⟩
  obtain ⟨hW,d,hd,hZ⟩:= vigor_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P (ExpSmall.bp_n hq.early.pos) (retainInitial hl hq hx).mass hb.mass
    (ht.mono (fun i h=> ht' i h))
  have h1 : durable q l p M m w t := by
    refine ⟨hW,?_⟩
    filter_upwards [ht,hx] with n hn h
    refine ⟨hn.1.slide ?_ le_rfl (by unfold pins; omega)
      (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),fun i hi x hx=>?_⟩
    · unfold leafNew
      linarith [hq.early.small,(Nat.cast_nonneg q.u : 0≤(q.u:ℝ)),(Nat.cast_nonneg q.s : 0≤(q.s:ℝ))]
    obtain ⟨j,hj,hs,_⟩:=hn.2.1 i hi
    exact (h.onTile j hj x (hs hx)).2.2.2
  refine ⟨t,h1,⟨hb.forecast,?_⟩,ht.mono fun i h j hj x hx=> (ht' i h).1 x ⟨j,hj,hx⟩,
    d,hd,hZ.mono (fun i h => h _)⟩
  filter_upwards [ht,hx,hb.mark] with n hn he hm
  intro i hi x hx
  obtain ⟨j,hj,hs,hc,hh⟩:=hn.2.1 i hi
  have hz : (t n).rooting x=(s n).rooting x := by
    unfold LeafMixture.rooting
    rw [LeafMixture.poller_eq (t n) hn.1.part hi hx,LeafMixture.poller_eq (s n) he.strength.part hj (hs hx),
      hh]
  have hH := hm j hj x (hs hx) (hc x hx)
  unfold engrave seems at hH ⊢; rwa [hz]

/-- Tiny cover exists after preparing retained mass, seen on
its support. Requires each old tile contain only original support. -/
def nebulous (q : PreparationParameters) (l : Filter ℕ) (s : rhythms p M) (w : tale p M) (P : Campaign p M)
    (b : Sketch p M) :=
   ∀ᶠ n in l,∃ T : Cov p (M*n),cdim p T≤q.d∧
     ∀ x,potion s w P n x≠0 → covered p T (delta (b.m n) x)

theorem hideOn (h : nebulous q l s w P b) (hb : q.citable l p M m w s b P)
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n)) :
    ∀ᶠ n in l,∃ T : Cov p (M*n),cdim p T≤q.d∧∀ i ∈ (s n).T,
       ∀ x∈i,P n x→covered p T (delta (b.m n) x) := by
  classical
  filter_upwards [hb.mass.positive,hx,h] with n hn h ht
  obtain ⟨T,hT,hc⟩:=ht
  refine ⟨T,hT,fun i hi x hx hp=> hc _ ?_⟩
  have hh := (h.onTile i hi x hx).1
  unfold potion
  have hm : 0< (s n).amount (w n) := lt_of_lt_of_le (by norm_num) h.weight
  have hv : (s n).sap (w n) x≠0 := by
    unfold LeafMixture.sap allW
    rw [onW_val,ind_one (show inTiles (s n).T x from ⟨i,hi,hx⟩),mul_one]
    exact div_ne_zero hh hm.ne'
  rw [onW_val,ind_one hp,mul_one]; exact div_ne_zero hv hn.ne'

set_option maxHeartbeats 1800000 in
theorem pressHarvest (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.citable l p M m w s b P)
    (hc : q.nebulous l s w P b) :
    ∃ t : rhythms p M, durable q l p M m w t ∧
      q.bright l p M m t b ∧
      (∀ᶠ n in l,q.hardened p (M*n) (t n) (b.m n)) ∧
      ∃ d,ExpSmall l (fun n=> ((M*n:ℕ):ℝ)) d ∧
        ∀ᶠ n in l,charm s w P b n-d n ≤ glow t w b n := by
  classical
  let N (n:ℕ) := M*n; let z (n:ℕ):=((N n):ℝ)
  let Y : Campaign p M := fun n=> inTiles (s n).T
  let E := fun i => bp (-(z i)) + bp (-q.ζ*z i)
  let R n (t : LeafMixture p n (M*n)) := t.strength (w n) (usual p (m n) (M*n))
    (q.leafOld+q.u+q.s+1) q.ζ q.pins ∧ pr (w n) (fun x=> Y n x ∧ P n x∧¬inTiles t.T x)≤ E n ∧
    ∃ T:Cov p (M*n), cdim p T ≤q.d ∧
        (∀ i∈(s n).T,∀ x∈i,P n x → covered p T (delta (b.m n) x)) ∧
        LeafMixture.elder (s n) t (P n)
         (fun i j=> specialLeaf T (b.m n) ((s n).pin j) i (t.pin i))
  obtain ⟨t,ht⟩ : ∃ t: rhythms p M,∀ᶠ n in l,R n (t n) := by
    refine taking ?_
    filter_upwards [hw,hx,hideOn hc hb hx,hq.wrap.filter_mono hl,
      ((trend_sizes l hl hq.hM).1.eventually (eventually_gt_atTop 0)),hb.mark]
      with n hn h ht hZ hN hh
    obtain ⟨T,hT,hL⟩:=ht
    have he := hq.early
    have hf (i) (hi:i∈(s n).T) (x) (hx:x∈i) (hp:P n x) j :
       b.m n x j∈effective ((s n).pin i).sp j := by
      have hz : (s n).rooting x=((s n).pin i).sp :=
        congrArg Pin.sp (LeafMixture.poller_eq (s n) h.strength.part hi hx)
      rw [←hz]; exact (((hh i hi x hx hp).1.1 j).2)
    obtain ⟨t,h1,h2,h3⟩ := LeafMixture.elder_weave h.strength he.pos hn.law (P n) (b.m n) T
      he.small hN (hZ.2.2.1 _) hT (fun i hi x hx hp=> ⟨hL i hi x hx hp,hf i hi x hx hp⟩)
      he.bigS hZ.2.1
    exact ⟨t,h1,h3,T,hT,hL,h2⟩
  have hz : Tendsto z l atTop := (trend_sizes l hl hq.hM).2
  let Q : Campaign p M := fun n=> inTiles (t n).T
  have ht' (i) : R i (t i) → (∀ x, Q i x → Y i x∧P i x) ∧
      pr (w i) (fun x=>Y i x∧P i x∧¬Q i x)≤E i := by
    rintro ⟨h,h',T,hi,hz,hg⟩; exact ⟨fun x hx=> LeafMixture.ancestral hg hx,h'⟩
  have hE : ExpSmall l z E := by
    unfold E
    convert ((ExpSmall.bp_n zero_lt_one).add hz (ExpSmall.bp_n hq.early.pos)) using 1
    simp
  obtain ⟨hW,d,hd,hZ⟩:= vigor_trim z hz w (hw.mono fun i h=>h.law.nz)
    Y Q P hE (retainInitial hl hq hx).mass hb.mass
    (ht.mono (fun i h=> ht' i h))
  have h1 : durable q l p M m w t := by
    refine ⟨hW,?_⟩
    filter_upwards [ht,hx] with n hn h
    obtain ⟨hi,_,T,hT,hC,hL⟩:=hn
    refine ⟨hi.slide ?_ ?_ le_rfl
      (fun x=> mul_nonneg (raw_nonneg _ _) (raw_nonneg _ _)),fun i hi x hx=>?_⟩
    · unfold leafNew; linarith
    · linarith only [hq.early.pos]
    obtain ⟨j,hj,hs,_⟩:=hL i hi
    exact (h.onTile j hj x (hs hx)).2.2.2
  have he (i : ℕ) (h : q.entered p (M*i) (m i) (w i) (s i)) (j) (hj:j∈(s i).T)
      (x) (hx:x∈j) : (s i).rooting x=((s i).pin j).sp :=
    congrArg Pin.sp (LeafMixture.poller_eq (s i) h.strength.part hj hx)
  refine ⟨t,h1,⟨hb.forecast,?_⟩,?_,d,hd,hZ.mono (fun i h=>h _)⟩
  · filter_upwards [ht,hx,hb.mark] with n hn he' hm
    intro i hi x hx
    obtain ⟨hT,_,T,_,_,hL⟩:=hn
    obtain ⟨j,hj,hs,hc,hV⟩:=hL i hi
    have hz : (s n).rooting x≤(t n).rooting x := by
      rw [he n he' j hj x (hs hx),LeafMixture.rooting,LeafMixture.poller_eq (t n) hT.part hi hx]
      exact hV.1
    obtain ⟨⟨hE,hA⟩,he,hy⟩:=hm j hj x (hs hx) (hc x hx)
    exact ⟨⟨fun i=>⟨(hE i).1,plan_inc_eff _ _ hz _ ((hE i).2)⟩,hA⟩,he,hy⟩
  · filter_upwards [ht,hx,hb.mark] with n hn he' hm
    obtain ⟨hT,_,T,hC,hD,hL⟩:=hn
    refine ⟨T,hC,fun i hi x hx=>?_,fun i hi=>?_⟩
    · obtain ⟨j,hj,hS,hE,_⟩:= hL i hi; exact hD j hj x (hS hx) (hE x hx)
    obtain ⟨j,hj,hS,hE,hH⟩:= hL i hi
    refine ⟨(s n).pin j,hH,fun x hx k=> ?_⟩
    rw [←he n he' j hj x (hS hx)]
    exact (((hm j hj x (hS hx) (hE x hx)).1.1 k).2)

end PreparationParameters
end HadwigerCounterexample

end

end OAI
