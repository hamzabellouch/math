import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays13
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
namespace ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open AlignmentScales RationalPivotPlan
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)
def height (h : Fin a→ℤ) (S : Finset (Fin a)) : ℤ := ∏ j∈S,h j
 

def coefficient (q₀ : ℕ) (h u : Fin a→ℤ) (e : Fin D.pairs) : ℤ :=
  height h (D.added e)/((q₀:ℤ)*height h (block D.index D.tail (D.owner e)))*height u (D.added e)

private lemma pairing (q₀ : ℕ) (b : Scale a) (U : Finset (Fin D.pairs)) (q : Fin D.pairs→ℤ) :
    (∑ e,(terminalShift D q₀ b U).toAdd e*q e)=
      ∑ e∈U,(qExponent D.index D.tail D.owner D.added q₀ b (e,1)).num*q e := by
  let π : Shifts D →* Multiplicative ℤ :=
    {toFun:=fun v=>Multiplicative.ofAdd (∑ e,v.toAdd e*q e)
     map_one':=by simp
     map_mul':=by intro x y; change Multiplicative.ofAdd (∑ e,(x.toAdd e+y.toAdd e)*q e)=_
                  simp [add_mul,Finset.sum_add_distrib] }
  have hπ (e : Fin D.pairs) : π (unitShift D e)=Multiplicative.ofAdd (q e) := by
    change Multiplicative.ofAdd (∑ f,(Pi.single e (1:ℤ) : Slots D) f*q f)=_
    simp [Pi.single_apply]
  have hlist (l : List (Fin D.pairs)) :
      π (FreeGroup.lift (letter D.index D.tail D.owner D.added (unitShift D) q₀ b)
        ((l.map (fun e=>FreeGroup.of (e,(1:ℚ)))).prod)) =
      Multiplicative.ofAdd ((l.map (fun e=>(qExponent D.index D.tail D.owner D.added q₀ b (e,1)).num*q e)).sum) := by
    induction l with
    | nil => simp
    | cons e l ih =>
      simp only [List.map_cons,List.prod_cons,map_mul,FreeGroup.lift_apply_of,letter,map_zpow,hπ,ih,List.sum_cons]
      rfl
  have he:=congrArg Multiplicative.toAdd (hlist U.toList)
  change (∑ e,(terminalShift D q₀ b U).toAdd e*q e) = _ at he
  rw [←List.sum_toFinset _ U.nodup_toList] at he
  simpa [mul_comm] using he

private lemma coefficient_exact (q₀ w : ℕ) (hq₀ : 0<q₀) (hw : q₀+1≤w)
    (h u : Fin a→ℤ) (hpos : ∀ j,0<h j) (e : Fin D.pairs)
    (hh : ∃ k : ℤ,height h (D.added e)=height h (block D.index D.tail (D.owner e))*((primorial w:ℤ)^w*k)) :
    (primorial w:ℤ)∣coefficient D q₀ h u e ∧
    (coefficient D q₀ h u e:ℚ)=
      ((height h (D.added e):ℚ)/((q₀:ℚ)*(height h (block D.index D.tail (D.owner e)):ℚ)))*height u (D.added e) := by
  obtain ⟨k,hk⟩:=hh
  have habs : (q₀:ℤ)*(primorial w:ℤ)∣(primorial w:ℤ)^w := by
    exact_mod_cast IntegerAlignment.fixed_mul_primorial_dvd hq₀ hw
  obtain ⟨d,hd⟩:=habs
  have hp : 0<height h (block D.index D.tail (D.owner e)) := Finset.prod_pos (fun j _=>hpos j)
  have hn : (q₀:ℤ)*height h (block D.index D.tail (D.owner e))≠0 := mul_ne_zero (by exact_mod_cast hq₀.ne') hp.ne'
  have he : height h (D.added e)=((q₀:ℤ)*height h (block D.index D.tail (D.owner e)))*((primorial w:ℤ)*d*k) := by
    rw [hk,hd]
    ring
  have hco : coefficient D q₀ h u e=((primorial w:ℤ)*d*k)*height u (D.added e) := by
    unfold coefficient
    rw [he,Int.mul_ediv_cancel_left _ hn]
  rw [hco]
  refine ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _,?_⟩
  rw [he]
  push_cast
  have hq : (q₀:ℚ)≠0 := by exact_mod_cast hq₀.ne'
  have hhp : (height h (block D.index D.tail (D.owner e)):ℚ)≠0 := by exact_mod_cast hp.ne'
  field_simp

 

theorem source_terminal_arithmetic (B : Finset (Scale a)) :
    ∃ Q : ℕ,0<Q ∧ ∀ q₀ : ℕ,0<q₀ → Q∣q₀ → ∀ w : ℕ,q₀+1≤w →
      ∀ b∈B,(∀ j,0<b j) → ∀ h u : Fin a→ℤ,(∀ j,0<h j) →
      (∀ e,∃ k : ℤ,height h (D.added e)=
        height h (block D.index D.tail (D.owner e))*((primorial w:ℤ)^w*k)) →
      (∀ e,(primorial w:ℤ)∣coefficient D q₀ h u e) ∧
      ∀ U : Finset (Fin D.pairs),
        (((∑ e,(terminalShift D q₀ b U).toAdd e*coefficient D q₀ h u e):ℤ):ℚ)=
          ∑ e∈U,((height h (D.added e):ℚ)*blockProduct b (D.added e)/
            ((height h (block D.index D.tail (D.owner e)):ℚ)*
              blockProduct b (block D.index D.tail (D.owner e))))*(height u (D.added e):ℚ)

 := by
  classical
  obtain ⟨Q,hQ,hclear⟩:=finite_denominator (B ×ˢ (Finset.univ : Finset (Fin D.pairs)))
    (fun be=>blockProduct be.1 (D.added be.2)/blockProduct be.1 (block D.index D.tail (D.owner be.2)))
  refine ⟨Q,hQ,?_⟩
  intro q₀ hq₀ hQq w hw b hb hbpos h u hh hratio
  have hc (e : Fin D.pairs):=coefficient_exact D q₀ w hq₀ hw h u hh e (hratio e)
  refine ⟨fun e=>(hc e).1,?_⟩
  intro U
  rw [pairing]
  push_cast
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨m,hm⟩:=hclear (b,e) (Finset.mem_product.mpr ⟨hb,Finset.mem_univ _⟩)
  obtain ⟨d,hd⟩:=hQq
  have hint : qExponent D.index D.tail D.owner D.added q₀ b (e,1)=((d:ℤ)*m:ℤ) := by
    dsimp [qExponent]
    rw [hd]
    push_cast
    calc
      (Q:ℚ)*d*1*(blockProduct b (D.added e)/blockProduct b (block D.index D.tail (D.owner e))) =
        (d:ℚ)*((Q:ℚ)*(blockProduct b (D.added e)/blockProduct b (block D.index D.tail (D.owner e)))) := by ring
      _ = _ := by rw [hm]
  have hn : ((qExponent D.index D.tail D.owner D.added q₀ b (e,1)).num:ℚ)=
      (q₀:ℚ)*(blockProduct b (D.added e)/blockProduct b (block D.index D.tail (D.owner e))) := by
    rw [hint,Rat.num_intCast]
    simpa [qExponent] using hint.symm
  rw [hn,(hc e).2]
  have hq : (q₀:ℚ)≠0 := by exact_mod_cast hq₀.ne'
  have hh0 : (height h (block D.index D.tail (D.owner e)):ℚ)≠0 := by
    exact_mod_cast (Finset.prod_pos (fun j _=>hh j) : 0<height h (block D.index D.tail (D.owner e))).ne'
  have hb0 : blockProduct b (block D.index D.tail (D.owner e))≠0 :=
    (Finset.prod_pos (fun j _=>hbpos j)).ne'
  field_simp

end ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels SourceExposureSlots SourceResidueAlignment ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open scoped BigOperators BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)
variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀
variable (G₀ : Fin D.targets→ℚ→Fin r→Type)
variable [∀ t v c,Group (G₀ t v c)] [∀ t v c,TopologicalSpace (G₀ t v c)]
variable (Γ₀ : ∀ t v c,Subgroup (G₀ t v c))
variable (M J R H : ℕ→ℕ) (L : ℕ→ℤ) (C : ℕ→Fin D.pairs→ℤ)
variable (g₀ x₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→G₀ t v c)
variable (obs₀ : ∀ t,ℕ→(Fin (h D t)→ℕ)→∀ v c,ℤ→ℤ→((G₀ t v c)⧸Γ₀ t v c) →ᵇ ℝ)
variable (ht : ℕ→Fin a→ℤ)
def heightCoeff (N : ℕ) (e : Fin D.pairs) : ℤ :=
  height (ht N) (D.added e)/((q₀:ℤ)*height (ht N) (block D.index D.tail (D.owner e)))
def readOriginal (N : ℕ) (u : Fin a→ℕ) (t : Fin D.targets) (v : ℚ) (col : Fin r) (n : ℤ) : ℝ :=
  pieceModel (Γ₀ t v col) (M N) (H N) (g₀ t N (outer D t u) v col)
    (x₀ t N (outer D t u) v col) (fun b r=>obs₀ t N (outer D t u) v col b r) n
def outcomeScales : Finset (Scale a) :=
  {1} ∪ (pivotOptions s r hs D Fs).biUnion (fun p=>Fs.image (fun d=>scaleRun D 0 p b₀*d))
def terminalDenom : ℕ :=
  (source_terminal_arithmetic D (outcomeScales D s r hs Fs b₀)).choose
def slots : Finset (Slots D) :=
  (pivotOptions s r hs D Fs).image (fun p=>jumpSlot D q₀ p b₀)
 

def pivotProperty (N : ℕ) (u : Fin a→ℕ) (x : ℕ) (τ : ℝ) : Prop :=
  ∃ p∈pivotOptions s r hs D Fs,∀ i : Comparison D Fs r,
    let t:=i.2.1.1
    let b:=scaleRun D 0 p b₀*i.1.val
    let av:=blockProduct b (block D.index D.tail t)
    ∃ Δ : ℤ,
      (Δ:ℚ)=∑ e∈i.2.1.2.val,
        ((height (ht N) (D.added e):ℚ)*blockProduct b (D.added e)/
          ((height (ht N) (block D.index D.tail (D.owner e)):ℚ)*
            blockProduct b (block D.index D.tail (D.owner e))))*
          (height (fun j=>(u j:ℤ)) (D.added e):ℚ) ∧
      (2*τ<readOriginal D r G₀ Γ₀ M H g₀ x₀ obs₀ N u t av i.2.2
        ((height (fun j=>(u j:ℤ)) (D.tail t))*(x:ℤ)) →
       τ<readOriginal D r G₀ Γ₀ M H g₀ x₀ obs₀ N u t av i.2.2
        ((height (fun j=>(u j:ℤ)) (D.tail t))*(x:ℤ)+Δ))
private lemma reading_inner_product (t : Fin D.targets) (u : Fin a→ℕ) :
    (∏ j : Fin (m D t),(inner D t u j:ℤ))=∏ j∈D.tail t,(u j:ℤ) := by
  have hi (j : Fin (m D t)) : perm D t (j.castAdd (h D t))=
      ((Fintype.equivFin {j : Fin a // j∈D.tail t}).symm j).val := by
    unfold perm
    rw [Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.trans_apply]
    rfl
  simp only [inner,hi]
  calc
    _ = ∏ j : {j : Fin a // j∈D.tail t},(u j.val:ℤ) :=
      (Fintype.equivFin {j : Fin a // j∈D.tail t}).symm.prod_comp _
    _ = ∏ j∈D.tail t,(u j:ℤ) := Finset.prod_coe_sort (D.tail t) (fun j : Fin a=>(u j:ℤ))
private lemma reading_coprime_mod {L t t' : ℤ} (ht : IsCoprime t L) (he : t'≡t [ZMOD L]) :
    IsCoprime t' L := by
  obtain ⟨k,hk⟩:=Int.modEq_iff_dvd.mp he
  obtain ⟨a,b,hab⟩:=ht
  refine ⟨a,b+a*k,?_⟩
  linear_combination hab-a*hk
private lemma reading_residue_congr {L t t' q : ℤ} (hL : 0<L) (ht : IsCoprime t L)
    (he : t'≡t [ZMOD L]) :
    SourceResidueAlignment.residue L t' q=SourceResidueAlignment.residue L t q := by
  have hs:=residue_spec L t q hL ht
  have hs':=residue_spec L t' q hL (reading_coprime_mod ht he)
  exact IntegerAlignment.residue_unique hL ht hs'.1 hs'.2.1 hs.1 hs.2.1
    ((he.symm.mul_right _).trans hs'.2.2) hs.2.2
private lemma reading_slotSum (N W : ℕ) (z : (Fin a→ℕ)×ℕ)
    (hL : 0<L N) (hWL : (W:ℤ)∣L N) (hc : ∀ e,(W:ℤ)∣C N e)
    (hu : ∀ j,IsCoprime (z.1 j:ℤ) (L N))
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e))) (v : Slots D) :
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ (fun t (i : I)=>G₀ t i.1.val.1 i.2) (qdim D)
      (fun t i=>Γ₀ t i.1.val.1 i.2) (coord D) ((d.atTime N).localModel z) v=
        slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) v := by
  let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
  let l:=(d.atTime N).localModel z
  let G:=fun t (i : I)=>G₀ t i.1.val.1 i.2
  let Γ:=fun t (i : I)=>Γ₀ t i.1.val.1 i.2
  have hf:=source_frozen_family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    N W z hL hWL hc hu hd
  have hmod (t : Fin D.targets) :
      (∏ j,(l.label t).residue j)≡(∏ j∈D.tail t,(z.1 j:ℤ)) [ZMOD L N] := by
    rw [←reading_inner_product D t z.1]
    apply Int.ModEq.prod
    intro j hj
    exact Int.mod_modEq _ _
  have hr (e : Fin D.pairs) : FiniteModelSlots.residue D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l e=
      rValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) e := by
    unfold FiniteModelSlots.residue FiniteModelSlots.coefficient
    rw [hf.2.1 e]
    apply reading_residue_congr hL
    · exact IsCoprime.prod_left (fun j _=>hu j)
    · exact hmod (D.owner e)
  change FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l v=_
  unfold FiniteModelSlots.slotSum slotValue
  simp_rw [hr]
private lemma reading_slot_bound (L : ℤ) (hL : 0<L) (c : Fin D.pairs→ℤ)
    (u : Fin a→ℤ) (hu : ∀j,IsCoprime (u j) L) (v : Slots D) :
    |slotValue D L c u v|≤(∑ e, |v e|)*L := by
  calc
    |slotValue D L c u v|≤∑e,|v e*rValue D L c u e|:=Finset.abs_sum_le_sum_abs _ _
    _≤∑ e, |v e| * L:=by
      apply Finset.sum_le_sum
      intro e he
      have hr:=residue_spec L (tailValue D u e) (qValue D c u e) hL
        (IsCoprime.prod_left (fun j _=>hu j))
      have hr0 : 0≤rValue D L c u e:=hr.1
      rw [abs_mul,abs_of_nonneg hr0]
      exact mul_le_mul_of_nonneg_left hr.2.1.le (abs_nonneg _)
    _=(∑ e, |v e|)*L:=by rw [Finset.sum_mul]
private lemma reading_scaleRun_pos (p : Path D) (hp : ∀o∈p,0<o.1) (j : ℕ)
    (b : Scale a) (hb : ∀l,0<b l) : ∀l,0<scaleRun D j p b l := by
  induction p generalizing j b with
  | nil => exact hb
  | cons o p ih =>
    apply ih (fun o ho=>hp o (List.mem_cons_of_mem _ ho))
    intro l
    exact mul_pos (hb l) (multiplier_pos D.index (tailAt D.tail j) (by exact_mod_cast hp o (List.mem_cons_self)) l)
private lemma reading_av_mem (p : Path D) (hp : p∈pivotOptions s r hs D Fs) (i : Comparison D Fs r) :
    FiniteModelSlots.centerAV D r Fs q₀ b₀ p i∈FiniteModelSlots.required D s r hs Fs q₀ b₀ ∧
    FiniteModelSlots.terminalAV D r Fs q₀ b₀ p i∈FiniteModelSlots.required D s r hs Fs q₀ b₀ := by
  constructor <;> apply Finset.mem_union_right <;> apply Finset.mem_biUnion.mpr <;>
    refine ⟨p,hp,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩⟩ <;> simp
private lemma reading_scalar (N : ℕ) (z : (Fin a→ℕ)×ℕ) (t : Fin D.targets) (av : ℚ×Slots D)
    (hav : av∈FiniteModelSlots.required D s r hs Fs q₀ b₀) (col : Fin r) (n : ℤ) :
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    FiniteModelSlots.scalar D s r hs Fs q₀ b₀ (fun t (i : I)=>G₀ t i.1.val.1 i.2) (qdim D)
      (fun t i=>Γ₀ t i.1.val.1 i.2) ((d.atTime N).localModel z) t
      (FiniteModelSlots.formula D s r hs Fs q₀ b₀ t av.1 av.2 col) n=
        readOriginal D r G₀ Γ₀ M H g₀ x₀ obs₀ N z.1 t av.1 col n := by
  unfold FiniteModelSlots.formula
  rw [dite_eq_left hav]
  rfl
 

theorem source_pivot_reading (N w : ℕ) (z : (Fin a→ℕ)×ℕ) (k p : ℕ)
    (hq₀ : 0<q₀) (hQq : terminalDenom D s r hs Fs b₀∣q₀) (hw : q₀+1≤w)
    (hL : 0<L N) (hWL : (primorial w:ℤ)∣L N) (hML : (M N:ℤ)∣L N)
    (hu : ∀ j,IsCoprime (z.1 j:ℤ) (L N))
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e)))
    (hb₀ : ∀ j,0<b₀ j) (hFs : ∀ b∈Fs,∀ j,0<b j)
    (hht : ∀ j,0<ht N j)
    (hratio : ∀ e,∃ d : ℤ,height (ht N) (D.added e)=
      height (ht N) (block D.index D.tail (D.owner e))*((primorial w:ℤ)^w*d))
    (hp : (p:ℤ)=firstPivot (M N) (J N) z.2+(M N:ℤ)*(k:ℤ))
    (hlarge : ∀ v∈slots D s r hs Fs q₀ b₀,(∑ e,|v e|)*L N<(p:ℤ)) (τ : ℝ) :
    let C:=heightCoeff D q₀ ht
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    ((d.atTime N).localModel z).modelSuccess (coord D) (k:ℤ) s r hs
      (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ →
    ∃ v∈slots D s r hs Fs q₀ b₀,
      let x:=(p:ℤ)+slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) v
      0<x ∧ pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N z.1 x.toNat τ
 := by
  dsimp only
  let C:=heightCoeff D q₀ ht
  let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
  let l:=(d.atTime N).localModel z
  let G:=fun t (i : I)=>G₀ t i.1.val.1 i.2
  let Γ:=fun t (i : I)=>Γ₀ t i.1.val.1 i.2
  have ht₁:=(source_terminal_arithmetic D (outcomeScales D s r hs Fs b₀)).choose_spec.2
    q₀ hq₀ hQq w hw 1 (by simp [outcomeScales]) (by intro j;exact zero_lt_one)
    (ht N) (fun _=>1) hht hratio
  have hc : ∀ e,(primorial w:ℤ)∣C N e := by
    intro e
    simpa [C,heightCoeff,coefficient,height] using ht₁.1 e
  have hf:=source_frozen_family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    N (primorial w) z hL hWL hc hu hd
  have hslt:=reading_slotSum D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    N (primorial w) z hL hWL hc hu hd
  intro hsuc
  have hn:=(source_family_numeric D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    N (primorial w) z hL hWL hc hu hd hML (k:ℤ) τ).mp hsuc
  rcases hn with ⟨o,ho,hnum⟩
  let v:=jumpSlot D q₀ o b₀
  have hv : v∈slots D s r hs Fs q₀ b₀:=Finset.mem_image.mpr ⟨o,ho,rfl⟩
  let x:=(p:ℤ)+slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) v
  have hbound:=reading_slot_bound D (L N) hL (C N) (fun j=>(z.1 j:ℤ)) hu v
  have hx : 0<x := by
    have hh:=hlarge v hv
    have hh':=neg_abs_le (slotValue D (L N) (C N) (fun j=>(z.1 j:ℤ)) v)
    dsimp [x]
    linarith
  refine ⟨v,hv,hx,o,ho,?_⟩
  intro i
  let b:=scaleRun D 0 o b₀*i.1.val
  have hb : b∈outcomeScales D s r hs Fs b₀:=Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨o,ho,Finset.mem_image.mpr ⟨i.1.val,i.1.property,rfl⟩⟩)
  have hbpos (j : Fin a) : 0<b j:=mul_pos
    (reading_scaleRun_pos D o (pivotOptions_paths s r hs D Fs o ho).2 0 b₀ hb₀ j)
    (hFs i.1.val i.1.property j)
  have ht₂:=(source_terminal_arithmetic D (outcomeScales D s r hs Fs b₀)).choose_spec.2
    q₀ hq₀ hQq w hw b hb hbpos (ht N) (fun j=>(z.1 j:ℤ)) hht hratio
  let Δ:=∑e,(terminalShift D q₀ b i.2.1.2.val).toAdd e*coefficient D q₀ (ht N) (fun j=>(z.1 j:ℤ)) e
  refine ⟨Δ,ht₂.2 i.2.1.2.val,?_⟩
  have hco (e : Fin D.pairs) : FiniteModelSlots.coefficient D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l e=
      coefficient D q₀ (ht N) (fun j=>(z.1 j:ℤ)) e := hf.2.1 e
  have hN : (∏j,((l.z i.2.1.1).1 j:ℤ))*(l.pstar i.2.1.1+(l.M:ℤ)*(k:ℤ)+
      FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l v)=
      height (fun j=>(z.1 j:ℤ)) (D.tail i.2.1.1)*(x.toNat:ℤ) := by
    change (∏j,(inner D i.2.1.1 z.1 j:ℤ))*(firstPivot (M N) (J N) z.2+(M N:ℤ)*(k:ℤ)+
      FiniteModelSlots.slotSum D s r hs Fs q₀ b₀ G (qdim D) Γ (coord D) l v)=_
    rw [reading_inner_product,←hp,hslt,Int.toNat_of_nonneg hx.le]
    rfl
  have hi:=hnum i
  dsimp only at hi
  rw [reading_scalar D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀ N z i.2.1.1
    (FiniteModelSlots.centerAV D r Fs q₀ b₀ o i) (reading_av_mem D s r hs Fs q₀ b₀ o ho i).1] at hi
  rw [reading_scalar D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀ N z i.2.1.1
    (FiniteModelSlots.terminalAV D r Fs q₀ b₀ o i) (reading_av_mem D s r hs Fs q₀ b₀ o ho i).2] at hi
  simp only [FiniteModelSlots.centerAV,FiniteModelSlots.terminalAV] at hi
  rw [hN] at hi
  dsimp only [G,Γ,l,d] at hco
  simp_rw [hco] at hi
  exact hi

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily

end
end

end OAI
