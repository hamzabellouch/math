import OAI.Combinatorics.HadwigerCounterexample.PreparationConditions

namespace OAI

/-! # Prepared Outcomes -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset
open scoped BigOperators Topology
open PredictionClass

namespace PreparationParameters
variable {l : Filter ℕ} {p : Shape} {M n N : ℕ} {q : PreparationParameters}
  {m : cycleM p} {s : rhythms p M} {w : tale p M}

theorem durable.gripped (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) :
    ∀ᶠ n in l,let N:=M*n; let v:=(s n).sap (w n); let x:=(s n).rooting;
    IsLaw v ∧ ∀ P:UnitType p n N×UnitType p n N→Prop, named P (bp (3*q.d*(N:ℝ))) →
      named (P ∘ Prod.swap) (bp (3*q.d*(N:ℝ))) →
    pr (pairW v v) (fun y=>P y∧¬secureAt p x y) ≤
      0.0005* pr (pairW v v) P +edgeError N := by
  let N (n:ℕ):=M*n
  let z (i:ℕ):=((N i):ℝ)
  have hz := (trend_sizes l hl hq.hM).2
  let a := (0.005:ℝ)
  have ha : 0<a:=by norm_num [a]
  filter_upwards [h.mass.inv_cap a ha, expO_const hz q.L a ha, h.shape,hq.wrap.filter_mono hl,
    hw,h.mass.positive] with n hn ht hh hB hW hS
  obtain ⟨h,hF⟩:=hh
  let v:=(s n).sap (w n)
  let C := ((s n).amount (w n))⁻¹
  have hc : 0≤C := (inv_pos_of_pos hS).le
  have hm : IsLaw v:= LeafMixture.sapLaw hS hW.law
  have hg : bySide p v (m n) (shine (N n)) := by
    refine LeafMixture.upperSide hW.border (LeafMixture.upper_sap hW.law hS) hc ?_
    rw [abs_of_nonneg hq.early.hL] at ht
    change |C|≤bp (a*z n) at hn
    rw [abs_of_nonneg hc] at hn
    refine (mul_le_mul hn ht hq.early.hL (bp_pos _).le).trans_eq ?_
    rw [←bp_add]; unfold a shine z; congr 1
    ring
  refine ⟨hm,fun P hp hP=> hB.2.2.2.2 P hp hP v (s n).rooting (m n)
    (LeafMixture.root_bound h) hm hg (fun x hx => ?_)⟩
  exact LeafMixture.in_parent hF (LeafMixture.present hx).1

theorem durable.unconditional (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) :
    ∀ᶠ n in l,let v:=(s n).sap (w n);
      pr (pairW v v) (fun x=>¬secureAt p (s n).rooting x) <0.01 ∧
      0.99 < pr (pairW v v) (secureAt p (s n).rooting) := by
  have he :
      ∀ᶠ n in l,edgeError (M*n)<0.0005 :=
    (((bp_tendsto_zero (by norm_num : 0 < (0.005:ℝ))).comp
      (trend_sizes l hl hq.hM).2).eventually (gt_mem_nhds (by norm_num)))
  filter_upwards [h.gripped hl hq hw,he] with n hn ht
  obtain ⟨hm,hg⟩:=hn
  let v:=(s n).sap (w n)
  let P := secureAt p (s n).rooting
  have hp : 1≤bp (3*q.d*((M*n:ℕ):ℝ)) := by
    rw [←bp_zero]; exact bp_le (by positivity)
  have hx := hg (fun _=>True) (named_true hp) (named_true hp)
  have hv : IsLaw (pairW v v):=pairW_law hm hm
  change pr (pairW v v) (fun x=>True∧¬P x) ≤ 0.0005*pr (pairW v v) (fun _=>True)+ _ at hx
  simp only [true_and,pr_true,hv.total,mul_one] at hx
  have hh : pr (pairW v v) (fun x=>¬P x)<0.01 := by linarith only [hx,ht]
  refine ⟨hh,?_⟩; rw [pr_not,hv.total] at hh
  linarith only [hh]

variable {b : Sketch p M}

theorem durable.kindles (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hf : ∀ᶠ n in l,0.04 ≤ glow s w b n) :
    glowOutcome l p M w s b := by
  refine ⟨0.02, by norm_num,?_⟩
  filter_upwards [h.gripped hl hq hw,h.unconditional hl hq hw,hf] with n hn ht hv
  obtain ⟨hm,_⟩:=hn
  have hi : gleam s w b n <0.01 :=
    lt_of_le_of_lt (pr_mono (pairW_law hm hm).nz (fun i hi=>hi.2)) ht.1
  have hg := gilding s w b n hm
  linarith only [hi,hg,hv]

def domed (q : PreparationParameters) (l : Filter ℕ) (s : rhythms p M) (b : Sketch p M) :=
  ∀ᶠ n in l, ∃ T : Cov p (M*n), cdim p T≤q.d ∧
    (s n).within (fun x=>covered p T (delta (b.m n) x))

theorem durable.domeLight (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) (hd : q.domed l s b) :
    ∀ᶠ n in l,gleam s w b n≤0.0005*glow s w b n+edgeError (M*n) := by
  classical
  filter_upwards [h.gripped hl hq hw,hd] with n hn hd
  obtain ⟨T,hT,hC⟩:= hd
  let v:=(s n).sap (w n)
  let P := matchProg b n
  obtain ⟨Q,h1,h2,h3⟩:= longStory T q.d hT b.c b.α b.r (delta (b.m n)) v
    (fun x hx=>LeafMixture.in_parent hC (LeafMixture.present hx).1)
  have hi : pr (pairW v v) Q=glow s w b n := avg_congr
    (fun x hx=> congrArg ind (propext (h3 x hx)))
  have hf : gleam s w b n=pr (pairW v v) (fun y=> Q y∧¬secureAt p (s n).rooting y) :=
    avg_congr (fun x hx=> congrArg ind (propext (and_congr_left fun _=>(h3 x hx).symm)))
  rw [hf,←hi]; exact hn.2 _ h1 h2

theorem durable.domeGlow (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n)) (hd : q.domed l s b)
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ᶠ n in l,δ ≤ glow s w b n) :
    glowOutcome l p M w s b := by
  have he : ∀ᶠ n in l,edgeError (M*n)<δ/4 := (((bp_tendsto_zero
    (by norm_num : 0<(0.005:ℝ))).comp
    (trend_sizes l hl hq.hM).2).eventually (gt_mem_nhds (by positivity)))
  refine ⟨δ/2,half_pos hδ,?_⟩
  filter_upwards [h.gripped hl hq hw,h.domeLight hl hq hw hd,he,hg] with n hn ht he hg
  have hh := gilding s w b n hn.1
  linarith only [hh,he,hg,hδ,ht]

theorem durable.domeSpark (h : durable q l p M m w s) (hl : l≤atTop) (hq : q.planted p M)
    (hw : ∀ᶠ n in l,q.nascent p (M*n) (w n) (m n))
    (hd : b.c=dusk)
    (hb : ∀ᶠ n in l,q.hardened p (M*n) (s n) (b.m n))
    {δ : ℝ} (hδ : 0<δ) (hg : ∀ᶠ n in l,δ/((M*n:ℕ):ℝ)^4 ≤ glow s w b n) :
    q.glimmer l p M w s b := by
  have hB := show q.domed l s b from hb.mono (fun i h => by
    obtain ⟨T,hT,hC,_⟩:=h; exact ⟨T,hT,hC⟩)
  let z n:=((M*n:ℕ):ℝ)
  have hz : Tendsto z l atTop := (trend_sizes l hl hq.hM).2
  have hi : ExpSmall l z (fun n=>edgeError (M*n)*(z n)^4) :=
    (ExpSmall.bp_n (by norm_num)).poly hz 4
  refine ⟨hd,δ,hδ,?_⟩
  filter_upwards [h.domeLight hl hq hw hB,hb,hg,hz.eventually (eventually_gt_atTop 0),
    (hi.lim hz).eventually (gt_mem_nhds (show 0<0.0005*δ from mul_pos (by norm_num) hδ))]
    with n h hb hg he hi
  refine ⟨hb,hg,h.trans ?_⟩
  have hz : edgeError (M*n) ≤ 0.0005*glow s w b n := calc
      _ ≤ 0.0005*δ/(z n)^4 := (le_div_iff₀ (by positivity)).mpr hi.le
      _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hg (by norm_num)
  linarith only [hz]

end PreparationParameters
end HadwigerCounterexample

end

end OAI
