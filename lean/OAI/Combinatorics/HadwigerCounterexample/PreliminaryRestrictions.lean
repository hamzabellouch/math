import OAI.Combinatorics.HadwigerCounterexample.PhasePreparedOutcomes

namespace OAI

/-! # Preliminary Restrictions -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix
open scoped BigOperators Topology
open PredictionClass
namespace PreparationParameters

variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters} {m : cycleM p}
  {s : rhythms p M} {w : tale p M} {b : Sketch p M} {P : Campaign p M}

def pollen : ℝ := 10^(-9:ℤ)
theorem pollen_pos : 0<pollen := by unfold pollen; positivity

structure dosed (q : PreparationParameters) (l : Filter ℕ) (p : Shape) (M : ℕ)
    (m : cycleM p) (w : tale p M) (s : rhythms p M) (b : Sketch p M) (P : Campaign p M) : Prop where
  cite : q.citable l p M m w s b P
  lower : ∀ᶠ n in l,pollen ≤ pr ((s n).sap (w n)) (P n)
  capped : ∀ᶠ n in l,∀ x i,totalRank (b.m n x i) ≤ q.e

theorem pollen_price :
    (pollen⁻¹:ℝ)*2≤bp 100 := by
  rw [show (100:ℝ)=(↑(100:ℕ):ℝ) from by norm_num,bp_nat]
  unfold pollen; norm_num

theorem potency {w : Wgt (UnitType p n N)} {s : LeafMixture p n N} (hw : IsLaw w)
    (hs : (1/2:ℝ)≤s.amount w) (P : UnitType p n N→Prop) (hP : pollen ≤ pr (s.sap w) P) (x) :
    onW (s.sap w) P x ≤ bp (100)*w x := by
  have hm:=LeafMixture.sapLaw (lt_of_lt_of_le (by norm_num) hs) hw
  have he (x) : s.sap w x ≤ 2*w x := (on_mon hw.nz (by norm_num) hs x).trans_eq (by norm_num)
  calc
    onW (s.sap w) P x ≤ (pollen)⁻¹* s.sap w x := on_mon hm.nz pollen_pos hP x
    _ ≤ _ := by
       refine (mul_le_mul_of_nonneg_left (he x) (inv_nonneg.mpr pollen_pos.le)).trans ?_
       rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right pollen_price (hw.nz _)

theorem dosed.stake (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P) :
    ∀ᶠ n in l, let N:=M*n; let v := potion s w P n
      IsLaw v ∧ bySide p v (m n) q.spear ∧ ∀ x,v x ≤ bp (q.spJoint*N)*usual p (m n) N x := by
  classical
  filter_upwards [hx,hw,hb.lower,hb.cite.on_law hl hq hw hx,
    (trend_sizes l hl hq.hM).2.eventually (eventually_ge_atTop 100)]
    with n hx hw h ht hN
  let N:=M*n; let v:=potion s w P n
  have hh (x) : v x ≤ bp (100)*w n x := potency hw.law hx.weight (P n) h x
  refine ⟨ht,LeafMixture.upperSide hw.border hh (bp_pos _).le le_rfl,fun x=>?_⟩
  apply (hh x).trans
  apply (mul_le_mul_of_nonneg_left (hw.total x) (bp_pos _).le).trans
  rw [←mul_assoc, ←bp_add]
  refine mul_le_mul_of_nonneg_right (bp_le ?_) (show 0≤usual p (m n) (M*n) x from
    mul_nonneg (raw_nonneg ..) (raw_nonneg ..))
  unfold spJoint; linarith only [hN]

private theorem epic_bounds (p : Shape) (z : BMark p n N) (x : UnitType p n N)
    (h : ∀ i,totalRank (z x i)≤q.e) :
    epoch p (delta z x) ≤ q.rank ∧ ∀ i,epoch p (mrAmbient z x i)≤ q.rank := by
  classical
  have hm i : epoch p (mrAmbient z x i) ≤ q.e :=
    (Finset.sum_le_sum (s:=Finset.univ) (g:=fun j:Comp p.g=>(z x i j).rank)
      (fun j _=> rank_lift_le _ _ _)).trans (h i)
  have hh : epoch p (delta z x) ≤
      epoch p (mrAmbient z x true)+epoch p (mrAmbient z x false) := by
    unfold epoch; rw [←Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => mrk_add_le ..
  have hi : q.e+q.e≤q.rank := by unfold rank; omega
  exact ⟨hh.trans ((add_le_add (hm _) (hm _)).trans hi),fun i=>(hm i).trans (by unfold rank; omega)⟩

set_option maxHeartbeats 900000 in
theorem phaseSplit (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (he : ∀ᶠ n in l, (s n).within
      (fun x=> P n x → delta (b.m n) x ≠ 0)) :
    ∃ R : Campaign p M, q.citable l p M m w s b R ∧ ∀ᶠ n in l,
      let v:=potion s w R n
      tonalMix p (delta (b.m n)) v ∨ tonalTiny p (delta (b.m n)) v q.d := by
  classical
  let c:=(tinyPhase p.g q.rank q.spJoint / 2)*(coin/2)
  have hc : 0<c := mul_pos (half_pos (tinyPhase_pos ..)) (by norm_num [coin])
  let v:=potion s w P
  let R n (A : UnitType p n (M*n) → Prop) :=
      c ≤ pr (v n) A ∧
        (tonalMix p (delta (b.m n)) (onW (v n) A) ∨ tonalTiny p (delta (b.m n)) (onW (v n) A) q.d)
  obtain ⟨A,hA⟩ : ∃ A : Campaign p M,∀ᶠ n in l, R n (A n) := by
    refine taking ?_
    filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hb.capped]
      with n hn ht hv he
    have hh (x) := epic_bounds p (b.m n) x (he x)
    change ∃ _,c≤_∧_
    refine phase_alternative (b.m n) (m n) (ht.2.2.2.1 _) hn.1 hn.2.1 hn.2.2 (fun x hx => ?_)
      (fun x=>(hh x).1)
    obtain ⟨hp,hx⟩:= onW_ne hx
    exact ⟨LeafMixture.in_parent hv (LeafMixture.present hx).1 hp,(hh x).2 _⟩
  have hx' : warm l (fun i=> ((M*i:ℕ):ℝ)) (fun i=>pr (v i) (A i)) :=
    (warm.const (trend_sizes l hl hq.hM).2 hc).mono (hA.mono fun i hi=>hi.1)
  obtain ⟨h1,h2⟩:= citable_interpose hw hx hb.cite hx'
  refine ⟨_,h1,?_⟩
  filter_upwards [h2,hA] with n hn ht
  dsimp only; rw [hn]
  exact ht.2

set_option maxHeartbeats 1200000 in
theorem phaseAbsent (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hx : ∀ᶠ n in l,q.entered p (M*n) (m n) (w n) (s n))
    (hb : q.dosed l p M m w s b P)
    (he : ∀ᶠ n in l,(s n).within
      (fun x=> P n x → delta (b.m n) x=0)) :
    satisfied q l p M m w := by
  classical
  obtain ⟨d,h1,h2⟩:=hq.room
  have hB : q.B<Fintype.card (Label p.b) := by
    have he : (↑(Fintype.card (Label p.b)):ℝ) = bp ((p.b:ℕ):ℝ) := by simp [Label,bp_nat,F,ZMod.card]
    exact_mod_cast (hq.hB.trans_le ((bp_le (by linarith [(Nat.cast_nonneg p.j :
      0≤(p.j:ℝ))])).trans_eq he.symm))
  have hS : 0≤q.spear := mul_nonneg (bp_pos _).le hq.early.hL
  obtain ⟨ε,hε,h⟩:= silicon_calendar p M q.e q.D d q.B hq.hM h1 hq.hD hB hq.hJ hq.hg hq.hR
    h2 q.spear hS
  refine byTorch hl hq hw hx hb.cite ?_
  filter_upwards [hb.stake hl hq hw hx,hq.wrap.filter_mono hl,he,hx,hb.cite.mark,h.filter_mono hl,
    hb.cite.forecast.small ε hε,hb.capped]
    with n hn ht hv hx hs hh hδ hz
  let v:= potion s w P n
  have heq (x) (hh : v x≠0) :
      (rawHoles (m n)).unit x ∧ joins x≤2*q.D ∧ frameSide p (m n) x ∧
        delta (b.m n) x=0 ∧ engrave b q m s n x := by
    obtain ⟨hp,hx'⟩:= onW_ne hh
    obtain ⟨⟨i,hi,hx'⟩,_⟩:= LeafMixture.present hx'
    obtain ⟨_,h1,h2,h3⟩:= hx.onTile i hi x hx'
    exact ⟨h1,h2,h3,hv i hi x hx' hp,hs i hi x hx' hp⟩
  have hi : b.α true=b.α false := by
    refine hh _ ht.1 v b.α (fun i=>b.g i n) hn.1 hn.2.1 (fun x hc=>?_)
    obtain ⟨_,h2,h3,h4,⟨h5,h6⟩,_,_⟩:=heq x hc
    refine ⟨h2,b.m n x,b.L n x,fun i=> ⟨(h5 i).1,(effective_mem.mp (h5 i).2).1,
      hz x i,h3 i⟩, zero_delta (b.m n) x h4,?_⟩
    exact fun i z h l g => (h6 i z h l g).trans hδ
  have hm (x) (h : pairW v v x≠0) :
      matchProg b n x := by
    have hx := heq x.1 (left_ne_zero_of_mul h)
    have hy := heq x.2 (right_ne_zero_of_mul h)
    refine fade b.c b.α b.r hb.cite.forecast.light hi (fun HD => ?_) _ x hx.2.2.2.1 hy.2.2.2.1
    obtain ⟨he,_,hF,hD,⟨hg,_⟩,hh,hx⟩:=hx
    exact hh.symm.trans (delta_dusk (m n) (b.m n) _ (fun i=>(effective_mem.mp (hg i).2).1)
      (hx HD) hD he hF)
  have hi : charm s w P b n=pr (pairW v v) (fun _=>True) := avg_congr (fun i hi=>
    (ind_one (hm i hi)).trans ind_true.symm)
  have hv : IsLaw v:=hn.1
  rw [hi,pr_true,(pairW_law hv hv).total]; norm_num

end PreparationParameters
end HadwigerCounterexample

end

end OAI
