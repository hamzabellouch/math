import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays10
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint
open SourceResidueAlignment ProductExposureLabels SourceMacroSelection
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
open scoped BigOperators BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace FiniteModelSlots
variable {a : ℕ} (D : Pivot a) (s r : ℕ) (hs : 1 ≤ s)
variable (Fs : Finset (Scale a)) (q₀ : ℕ) (b : Scale a)

def centerAV (p : Path D) (i : Comparison D Fs r) : ℚ×Slots D :=
  (blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail i.2.1.1),jumpSlot D q₀ p b)
def terminalAV (p : Path D) (i : Comparison D Fs r) : ℚ×Slots D :=
  ((centerAV D r Fs q₀ b p i).1,
    (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd+(centerAV D r Fs q₀ b p i).2)
 

def required : Finset (ℚ×Slots D) :=
  {(1,0)} ∪ (pivotOptions s r hs D Fs).biUnion (fun p=>Finset.univ.biUnion
    (fun i : Comparison D Fs r=>{centerAV D r Fs q₀ b p i,terminalAV D r Fs q₀ b p i}))
abbrev Index := {av : ℚ×Slots D // av∈required D s r hs Fs q₀ b} × Fin r

def formula (_t : Fin D.targets) (a₀ : ℚ) (v : Slots D) (col : Fin r) : Index D s r hs Fs q₀ b :=
  if h : (a₀,v)∈required D s r hs Fs q₀ b then (⟨(a₀,v),h⟩,col)
  else (⟨(1,0),by simp [required]⟩,col)

variable (G : Fin D.targets→Index D s r hs Fs q₀ b→Type)
variable [∀ t i,Group (G t i)] [∀ t i,TopologicalSpace (G t i)]
variable (q : Fin D.targets→ℕ) (Γ : ∀ t i,Subgroup (G t i))
variable (coord : ∀ e,Fin (q (D.owner e)))
variable (d : LocalModels D G q Γ)

def coefficient (e : Fin D.pairs) : ℤ := d.qval (D.owner e) (coord e)
def residue (e : Fin D.pairs) : ℤ := residueData d.L
  (coefficient D s r hs Fs q₀ b G q Γ coord d e) (d.label (D.owner e))
def slotSum (v : Slots D) : ℤ := ∑ e,v e*residue D s r hs Fs q₀ b G q Γ coord d e
 
def compile : LocalModels D G q Γ :=
  { d with slot:=fun _ i=>slotSum D s r hs Fs q₀ b G q Γ coord d i.1.val.2 }
def scalar (t : Fin D.targets) (i : Index D s r hs Fs q₀ b) (N : ℤ) : ℝ :=
  pieceModel (Γ t i) d.M (d.H t) (d.g t i) (d.x t i) (fun j l=>d.obs t i j l) N
 

def numericSuccess (k : ℤ) (τ : ℝ) : Prop :=
  ∃ p∈pivotOptions s r hs D Fs,∀ i : Comparison D Fs r,
    let t:=i.2.1.1
    let av:=centerAV D r Fs q₀ b p i
    let av':=terminalAV D r Fs q₀ b p i
    let z:=(terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd
    let N:=(∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+slotSum D s r hs Fs q₀ b G q Γ coord d av.2)
    2*τ<scalar D s r hs Fs q₀ b G q Γ d t (formula D s r hs Fs q₀ b t av.1 av.2 i.2.2) N →
      τ<scalar D s r hs Fs q₀ b G q Γ d t (formula D s r hs Fs q₀ b t av'.1 av'.2 i.2.2)
        (N+∑ e,z e*coefficient D s r hs Fs q₀ b G q Γ coord d e)

private lemma center_mem (p : Path D) (hp : p∈pivotOptions s r hs D Fs) (i : Comparison D Fs r) :
    centerAV D r Fs q₀ b p i∈required D s r hs Fs q₀ b := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨p,hp,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩⟩
  simp
private lemma terminal_mem (p : Path D) (hp : p∈pivotOptions s r hs D Fs) (i : Comparison D Fs r) :
    terminalAV D r Fs q₀ b p i∈required D s r hs Fs q₀ b := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨p,hp,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,?_⟩⟩
  simp
private lemma formula_val (t : Fin D.targets) (av : ℚ×Slots D)
    (hav : av∈required D s r hs Fs q₀ b) (col : Fin r) :
    (formula D s r hs Fs q₀ b t av.1 av.2 col).1.val=av := by
  simp [formula,hav]

private lemma terminal_support (t : Fin D.targets) (U : Finset (Fin D.pairs))
    (hU : ∀ e∈U,D.owner e=t) (e : Fin D.pairs) (he : D.owner e≠t) :
    (terminalShift D q₀ b U).toAdd e=0 := by
  let π : Shifts D →* Multiplicative ℤ :=
    {toFun:=fun v=>Multiplicative.ofAdd (v.toAdd e),map_one':=rfl,map_mul':=fun _ _=>rfl}
  have hh : π (terminalShift D q₀ b U)=1 := by
    simp only [terminalShift,baseWord,map_list_prod,List.map_map]
    apply List.prod_eq_one
    intro z hz
    obtain ⟨f,hf,rfl⟩:=List.mem_map.mp hz
    simp only [Function.comp_apply,FreeGroup.lift_apply_of,letter]
    change π ((unitShift D f)^(qExponent D.index D.tail D.owner D.added q₀ b (f,1)).num)=1
    rw [map_zpow]
    have hfe : e≠f := by
      intro hef
      subst f
      exact he (hU e (Finset.mem_toList.mp hf))
    have hπ : π (unitShift D f)=1 := by
      change (Pi.single f (1:ℤ) : Slots D) e=0
      simp [hfe]
    rw [hπ,one_zpow]
  exact hh

private lemma input_pairing (t : Fin D.targets) (v : Slots D)
    (hv : ∀ e,D.owner e≠t → v e=0) (f : Fin (q t)→ℤ) (A : Fin D.pairs→ℤ)
    (ha : ∀ e (h : D.owner e=t),A e=f (h ▸ coord e)) :
    (∑ j,f j*ownInput D q coord t v j)=∑ e,v e*A e := by
  classical
  simp only [ownInput,Finset.sum_apply,zsmul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ j,f j*(v e*ownBasis D q coord t e j)) = v e*∑ j,f j*ownBasis D q coord t e j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = v e*A e := by
      by_cases he : D.owner e=t
      · subst t
        rw [ha e rfl]
        simp [ownBasis,Pi.single_apply]
      · rw [hv e he]
        simp

private lemma slotSum_add (v z : Slots D) :
    slotSum D s r hs Fs q₀ b G q Γ coord d (v+z)=
      slotSum D s r hs Fs q₀ b G q Γ coord d v+slotSum D s r hs Fs q₀ b G q Γ coord d z := by
  simp [slotSum,add_mul,Finset.sum_add_distrib]

private lemma compile_value (k : ℤ) (t : Fin D.targets) (av : ℚ×Slots D)
    (hav : av∈required D s r hs Fs q₀ b) (col : Fin r) (u : Fin (q t)→ℤ) :
    (compile D s r hs Fs q₀ b G q Γ coord d).value k t
      (formula D s r hs Fs q₀ b t av.1 av.2 col) u =
    scalar D s r hs Fs q₀ b G q Γ d t (formula D s r hs Fs q₀ b t av.1 av.2 col)
      ((∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+slotSum D s r hs Fs q₀ b G q Γ coord d av.2)+
        (d.M:ℤ)*∑ e,shift d.M d.L (d.qval t e) (d.label t) (fun j=>((d.z t).1 j:ℤ))*u e) := by
  change scalar D s r hs Fs q₀ b G q Γ d t (formula D s r hs Fs q₀ b t av.1 av.2 col)
    ((∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+
      slotSum D s r hs Fs q₀ b G q Γ coord d (formula D s r hs Fs q₀ b t av.1 av.2 col).1.val.2)+
        (d.M:ℤ)*∑ e,shift d.M d.L (d.qval t e) (d.label t) (fun j=>((d.z t).1 j:ℤ))*u e)=_
  rw [formula_val D s r hs Fs q₀ b t av hav col]

private lemma numeric_shift (t : Fin D.targets) (k : ℤ) (v z : Slots D)
    (hz : ∀ e,D.owner e≠t → z e=0) (hL : 0<d.L) (hML : (d.M:ℤ)∣d.L)
    (hcop : IsCoprime (∏ j,(d.label t).residue j) d.L) :
    (∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+slotSum D s r hs Fs q₀ b G q Γ coord d (z+v))+
      (d.M:ℤ)*∑ e,shift d.M d.L (d.qval t e) (d.label t) (fun j=>((d.z t).1 j:ℤ))*ownInput D q coord t z e =
    (∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+slotSum D s r hs Fs q₀ b G q Γ coord d v)+
      ∑ e,z e*coefficient D s r hs Fs q₀ b G q Γ coord d e := by
  have hr : (∑ j,residueData d.L (d.qval t j) (d.label t)*ownInput D q coord t z j)=
      slotSum D s r hs Fs q₀ b G q Γ coord d z := by
    apply input_pairing D q coord t z hz
    intro e he
    subst t
    rfl
  have hq : (∑ j,d.qval t j*ownInput D q coord t z j)=
      ∑ e,z e*coefficient D s r hs Fs q₀ b G q Γ coord d e := by
    apply input_pairing D q coord t z hz
    intro e he
    subst t
    rfl
  have he:=source_number_terminal (v:=0) d.M d.L hL hML (d.R:ℝ) (d.z t) hcop
    (d.pstar t) (slotSum D s r hs Fs q₀ b G q Γ coord d v) (fun _ : Fin 1=>1) (fun _=>k)
    (d.qval t) (ownInput D q coord t z)
  simp only [number,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.zero_add,one_nsmul,one_mul] at he
  change (∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+
      (slotSum D s r hs Fs q₀ b G q Γ coord d v+
        ∑ j,residueData d.L (d.qval t j) (d.label t)*ownInput D q coord t z j))+
      (d.M:ℤ)*∑ e,shift d.M d.L (d.qval t e) (d.label t) (fun j=>((d.z t).1 j:ℤ))*ownInput D q coord t z e =
    (∏ j,((d.z t).1 j:ℤ))*(d.pstar t+(d.M:ℤ)*k+slotSum D s r hs Fs q₀ b G q Γ coord d v)+
      ∑ j,d.qval t j*ownInput D q coord t z j at he
  rw [hr,hq] at he
  rw [slotSum_add,add_comm (slotSum D s r hs Fs q₀ b G q Γ coord d z)]
  exact he

 

theorem source_numeric_success (k : ℤ) (τ : ℝ) (hL : 0<d.L) (hML : (d.M:ℤ)∣d.L)
    (hcop : ∀ t,IsCoprime (∏ j,(d.label t).residue j) d.L) :
    (compile D s r hs Fs q₀ b G q Γ coord d).modelSuccess coord k s r hs
      (formula D s r hs Fs q₀ b) Fs q₀ b τ ↔
    numericSuccess D s r hs Fs q₀ b G q Γ coord d k τ

 := by
  classical
  have hc (p : Path D) (hp : p∈pivotOptions s r hs D Fs) (i : Comparison D Fs r) :=
    compile_value D s r hs Fs q₀ b G q Γ coord d k i.2.1.1 (centerAV D r Fs q₀ b p i)
      (center_mem D s r hs Fs q₀ b p hp i) i.2.2 0
  have ht (p : Path D) (hp : p∈pivotOptions s r hs D Fs) (i : Comparison D Fs r) :=
    compile_value D s r hs Fs q₀ b G q Γ coord d k i.2.1.1 (terminalAV D r Fs q₀ b p i)
      (terminal_mem D s r hs Fs q₀ b p hp i) i.2.2
        (ownInput D q coord i.2.1.1 (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd)
  simp only [LocalModels.modelSuccess,numericSuccess]
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro i
  have hc':=hc p hp i
  have ht':=ht p hp i
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,add_zero] at hc'
  have hn:=numeric_shift D s r hs Fs q₀ b G q Γ coord d i.2.1.1 k (jumpSlot D q₀ p b)
    (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val).toAdd
    (terminal_support D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.1 i.2.1.2.val i.2.1.2.property)
    hL hML (hcop i.2.1.1)
  dsimp only [terminalAV,centerAV] at hc' ht'
  rw [hn] at ht'
  dsimp only [terminalAV,centerAV]
  rw [hc',ht']

end FiniteModelSlots
end SourceIntegerArrays.GlobalJoint
end

noncomputable section
namespace SourceIntegerArrays.GlobalJoint.SourceExposureSlots
open SourceResidueAlignment
open ConstructedWordPlan.GlobalWordPlan
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)
 

def qValue (c : Fin D.pairs→ℤ) (u : Fin a→ℤ) (e : Fin D.pairs) : ℤ :=
  c e*∏ j∈D.added e,u j
def tailValue (u : Fin a→ℤ) (e : Fin D.pairs) : ℤ :=
  ∏ j∈D.tail (D.owner e),u j
def rValue (L : ℤ) (c : Fin D.pairs→ℤ) (u : Fin a→ℤ) (e : Fin D.pairs) : ℤ :=
  SourceResidueAlignment.residue L (tailValue D u e) (qValue D c u e)
def slotValue (L : ℤ) (c : Fin D.pairs→ℤ) (u : Fin a→ℤ) (v : Slots D) : ℤ :=
  ∑ e,v e*rValue D L c u e

private lemma coprime_mod_congr {L t t' : ℤ} (ht : IsCoprime t L) (he : t'≡t [ZMOD L]) :
    IsCoprime t' L := by
  obtain ⟨k,hk⟩:=Int.modEq_iff_dvd.mp he
  obtain ⟨a,b,hab⟩:=ht
  refine ⟨a,b+a*k,?_⟩
  linear_combination hab-a*hk

private lemma residue_congr {L t t' q q' : ℤ} (hL : 0<L) (ht : IsCoprime t L)
    (he : t'≡t [ZMOD L]) (hq : q'≡q [ZMOD L]) :
    SourceResidueAlignment.residue L t' q'=SourceResidueAlignment.residue L t q := by
  have hs:=residue_spec L t q hL ht
  have hs':=residue_spec L t' q' hL (coprime_mod_congr ht he)
  exact IntegerAlignment.residue_unique hL ht hs'.1 hs'.2.1 hs.1 hs.2.1
    ((he.symm.mul_right _).trans (hs'.2.2.trans hq)) hs.2.2

private lemma residue_dvd {L W t q : ℤ} (hL : 0<L) (hWL : W∣L)
    (ht : IsCoprime t L) (hq : W∣q) : W∣SourceResidueAlignment.residue L t q := by
  have hspec:=residue_spec L t q hL ht
  have he : W∣q-t*SourceResidueAlignment.residue L t q := hWL.trans (Int.modEq_iff_dvd.mp hspec.2.2)
  have hm : W∣t*SourceResidueAlignment.residue L t q := by
    have hh:=dvd_sub hq he
    rw [show q-(q-t*SourceResidueAlignment.residue L t q)=t*SourceResidueAlignment.residue L t q by ring] at hh
    exact hh
  have hcop : IsCoprime W t := by
    obtain ⟨k,hk⟩:=hWL
    obtain ⟨a,b,hab⟩:=ht
    refine ⟨b*k,a,?_⟩
    rw [hk] at hab
    linear_combination hab
  exact hcop.dvd_of_dvd_mul_left hm

 

theorem source_exposure_slots (L W : ℤ) (hL : 0<L) (hWL : W∣L)
    (c : Fin D.pairs→ℤ) (hc : ∀ e,W∣c e)
    (u u' : Fin a→ℤ) (hu : ∀ j,IsCoprime (u j) L)
    (t : Fin D.targets)
    (hint : ∀ j∈D.tail t,u' j≡u j [ZMOD L])
    (hout : ∀ j,j∉D.tail t → u' j=u j)
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e))) :
    (∀ e,rValue D L c u' e=rValue D L c u e) ∧
    (∀ e,D.owner e=t → qValue D c u' e=qValue D c u e) ∧
    ∀ v : Slots D,
      slotValue D L c u' v=slotValue D L c u v ∧
      W∣slotValue D L c u v ∧
      |slotValue D L c u v|≤(∑ e,|v e|)*L

 := by
  classical
  have hh (j : Fin a) : u' j≡u j [ZMOD L] := by
    by_cases hj : j∈D.tail t
    · exact hint j hj
    · rw [hout j hj]
  have htail (e : Fin D.pairs) : IsCoprime (tailValue D u e) L :=
    IsCoprime.prod_left (fun j _=>hu j)
  have hr (e : Fin D.pairs) : rValue D L c u' e=rValue D L c u e := by
    apply residue_congr hL (htail e)
    · exact Int.ModEq.prod (fun j _=>hh j)
    · exact (Int.ModEq.prod (s:=D.added e) (fun j _=>hh j)).mul_left (c e)
  refine ⟨hr,?_,?_⟩
  · intro e he
    unfold qValue
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    apply hout j
    intro hjt
    exact Finset.disjoint_left.mp (hd e) hj (by simpa [he] using hjt)
  · intro v
    refine ⟨?_,?_,?_⟩
    · exact Finset.sum_congr rfl (fun e _=>congrArg (fun x=>v e*x) (hr e))
    · apply Finset.dvd_sum
      intro e _
      exact dvd_mul_of_dvd_right (residue_dvd hL hWL (htail e) (dvd_mul_of_dvd_left (hc e) _)) _
    · calc
        |slotValue D L c u v| ≤ ∑ e,|v e*rValue D L c u e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ e,|v e| * L := by
          apply Finset.sum_le_sum
          intro e _
          have hs:=residue_spec L (tailValue D u e) (qValue D c u e) hL (htail e)
          have hr0 : 0≤rValue D L c u e:=hs.1
          rw [abs_mul,abs_of_nonneg hr0]
          exact mul_le_mul_of_nonneg_left hs.2.1.le (abs_nonneg _)
        _ = (∑ e,|v e|)*L := by rw [Finset.sum_mul]

end SourceIntegerArrays.GlobalJoint.SourceExposureSlots

end
end

end OAI
