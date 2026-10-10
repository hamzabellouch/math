import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays14
import OAI.Combinatorics.SumProduct.Alignment.PivotExtension01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
end

noncomputable section
namespace SourcePivotExtension
open MeasureTheory ProductExposureLaw ProductExposureLabels RoughFaceShift RawHarmonicProbability
open SourceIntegerArrays
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private lemma unit_atom_pos (X W : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (p : ℕ) (hp : p∈units X W) : 0<(law X W hW hX:Measure ℕ).real {p} := by
  have hp0 : 0<p := by
    have ht:=(Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    omega
  rw [MicrocellConditional.law_apply_units]
  have he : MicrocellConditional.eventMass (units X W) {p}=(p:ℝ)⁻¹ := by
    simp [MicrocellConditional.eventMass,hp]
  rw [he]
  exact div_pos (inv_pos.mpr (by exact_mod_cast hp0)) (mass_pos X W hW hX)

private lemma outside_atom_pos {m : ℕ} (X : Fin m→ℕ) (W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (y : Fin m→ℕ) (hy : y∈outsideDomain X W) :
    0<(outsideLaw X W hW hX).real {y} := by
  simp only [outsideLaw,measureReal_def,Measure.pi_singleton,ENNReal.toReal_prod]
  apply Finset.prod_pos
  intro j hj
  exact unit_atom_pos (X j) W hW (hX j) (y j) (Fintype.mem_piFinset.mp hy j)

private lemma label_source_cell (M J p q : ℕ) (hM : 0<M) (hJ : 0<J) :
    q∈sourceCell M J p ↔ q/(M*J)=p/(M*J) ∧ q%M=p%M := by
  unfold sourceCell MicrocellFibers.fiber
  simp only [Finset.mem_filter,Finset.mem_Ico]
  have hw:=MicrocellSaturation.quotient_window (M*J) q (Nat.mul_pos hM hJ)
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hr⟩
    exact ⟨Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith),hr⟩
  · rintro ⟨hq,hr⟩
    rw [hq] at hw
    exact ⟨⟨by nlinarith [hw.1],by nlinarith [hw.2]⟩,hr⟩

private lemma full_support_mem {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (u : (Fin m→ℕ)×ℕ) :
    u∈fullDomain X Xp W ↔ u.1∈outsideDomain X W ∧ u.2∈units Xp W := by
  rcases u with ⟨y,p⟩
  simp only [fullDomain,rawDomain,outsideDomain,units,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product]
  tauto

private lemma raw_cell_product {m : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (z : (Fin m→ℕ)×ℕ) (hz : z.1∈outsideDomain X W) :
    (conditioningCell X Xp W M J z:Set _)={z.1} ×ˢ
      (((units Xp W).filter (fun p=>p/(M*J)=z.2/(M*J) ∧ p%M=z.2%M)):Set ℕ) := by
  ext u
  simp only [Finset.mem_coe,conditioningCell,Finset.mem_filter]
  rw [full_support_mem]
  simp only [conditioningLabel,Prod.mk.injEq,Set.mem_prod,Set.mem_singleton_iff,
    Finset.mem_coe,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hu,hp⟩,hy,hq,hr⟩
    exact ⟨hy,hp,hq,hr⟩
  · rintro ⟨hy,hp,hq,hr⟩
    exact ⟨⟨hy.symm ▸ hz,hp⟩,hy,hq,hr⟩

private lemma joint_rectangle_real {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (y : Fin m→ℕ) (S : Set ℕ) :
    (jointLaw X Xp W hW hX hXp).real ({y}×ˢS)=
      (outsideLaw X W hW hX).real {y}*(law Xp W hW hXp:Measure ℕ).real S := by
  change ((outsideLaw X W hW hX).prod (law Xp W hW hXp:Measure ℕ)).real ({y}×ˢS)=_
  rw [measureReal_def,Measure.prod_prod,ENNReal.toReal_mul]
  rfl

 

theorem conditional_slot_source_ratio {m V : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (hM : 0<M) (hJ : 0<J) (z : (Fin m→ℕ)×ℕ) (hz : z.1∈outsideDomain X W)
    (slot : Fin V→(Fin m→ℕ)→ℤ) (A : (Fin m→ℕ)→Set ℤ) :
    conditionalSlotMass X Xp W M J hW hX hXp slot A z=
      cellRatio Xp W M J z.2 hW hXp
        {k | (z.1,MicrocellFibers.point M (J*(z.2/(M*J))) (z.2%M) k)∈slotEvent slot A}
 := by
  let F : Finset ℕ := (units Xp W).filter (fun p=>p/(M*J)=z.2/(M*J) ∧ p%M=z.2%M)
  let C : Set ℕ := {p | (z.1,p)∈slotEvent slot A}
  let ν : Measure ℕ := (law Xp W hW hXp:Measure ℕ)
  have heC : (conditioningCell X Xp W M J z:Set _)={z.1}×ˢ(F:Set ℕ) :=
    raw_cell_product X Xp W M J z hz
  have heN : slotEvent slot A ∩ (conditioningCell X Xp W M J z:Set _) =
      {z.1}×ˢ(C∩(F:Set ℕ)) := by
    rw [heC]
    ext u
    simp only [Set.mem_inter_iff,Set.mem_prod,Set.mem_singleton_iff]
    constructor
    · rintro ⟨hu,hy,hp⟩
      have he : u=(z.1,u.2):=Prod.ext hy rfl
      exact ⟨hy,(congrArg (fun t=>t∈slotEvent slot A) he).mp hu,hp⟩
    · rintro ⟨hy,hu,hp⟩
      have he : u=(z.1,u.2):=Prod.ext hy rfl
      exact ⟨(congrArg (fun t=>t∈slotEvent slot A) he).mpr hu,hy,hp⟩
  have hr : conditionalSlotMass X Xp W M J hW hX hXp slot A z=
      ν.real (C∩(F:Set ℕ))/ν.real (F:Set ℕ) := by
    unfold conditionalSlotMass
    rw [heN,heC,joint_rectangle_real,joint_rectangle_real]
    exact mul_div_mul_left _ _ (outside_atom_pos X W hW hX z.1 hz).ne'
  have hF : (F:Set ℕ)=(units Xp W:Set ℕ)∩(sourceCell M J z.2:Set ℕ) := by
    ext p
    simp only [F,Finset.mem_coe,Finset.mem_filter,Set.mem_inter_iff,
      label_source_cell M J z.2 p hM hJ]
  have hf : ν.real (F:Set ℕ)=ν.real (sourceCell M J z.2:Set ℕ) := by
    rw [hF]
    apply measureReal_congr
    filter_upwards [law_ae_units Xp W hW hXp] with p hp
    exact propext ⟨fun h=>h.2,fun h=>⟨hp,h⟩⟩
  have hn : ν.real (C∩(F:Set ℕ))=ν.real (C∩(sourceCell M J z.2:Set ℕ)) := by
    rw [hF]
    apply measureReal_congr
    filter_upwards [law_ae_units Xp W hW hXp] with p hp
    exact propext ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,hp,h.2⟩⟩
  have himage : (MicrocellFibers.point M (J*(z.2/(M*J))) (z.2%M) ''
      {k | (z.1,MicrocellFibers.point M (J*(z.2/(M*J))) (z.2%M) k)∈slotEvent slot A}) ∩
      (sourceCell M J z.2:Set ℕ) = C∩(sourceCell M J z.2:Set ℕ) := by
    ext p
    constructor
    · rintro ⟨⟨k,hk,rfl⟩,hp⟩
      exact ⟨hk,hp⟩
    · rintro ⟨hp,hC⟩
      obtain ⟨k,hk⟩:=MicrocellFibers.represent M J (J*(z.2/(M*J))) (z.2%M) p hM hC
      refine ⟨⟨k.val,?_,hk⟩,hC⟩
      change (z.1,MicrocellFibers.point M (J*(z.2/(M*J))) (z.2%M) k.val)∈slotEvent slot A
      rw [hk]
      exact hp
  rw [hr,hf,hn]
  unfold cellRatio
  rw [himage]

end SourcePivotExtension
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
open MeasureTheory SourcePivotExtension RawHarmonicProbability ProductExposureLaw
abbrev slotCount := Fintype.card {v : Slots D // v∈slots D s r hs Fs q₀ b₀}
def rawSlot (N : ℕ) (v : Fin (slotCount D s r hs Fs q₀ b₀)) (u : Fin a→ℕ) : ℤ :=
  slotValue D (L N) (heightCoeff D q₀ ht N) (fun j=>(u j:ℤ))
    ((Fintype.equivFin {v : Slots D // v∈slots D s r hs Fs q₀ b₀}).symm v).val
def pivotSet (N : ℕ) (τ : ℝ) (u : Fin a→ℕ) : Set ℤ :=
  {x | 0<x ∧ pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N u x.toNat τ}
 

theorem source_posterior_domination (N w : ℕ) (z : (Fin a→ℕ)×ℕ)
    (X : Fin a→ℕ) (Xp : ℕ)
    (hW : 0<primorial w) (hX : ∀ j,4*primorial w≤X j) (hXp : 4*primorial w≤Xp)
    (hz : z.1∈outsideDomain X (primorial w)) (hM : 0<M N) (hJ : 0<J N)
    (hq₀ : 0<q₀) (hQq : terminalDenom D s r hs Fs b₀∣q₀) (hw : q₀+1≤w)
    (hL : 0<L N) (hWL : (primorial w:ℤ)∣L N) (hML : (M N:ℤ)∣L N)
    (hu : ∀ j,IsCoprime (z.1 j:ℤ) (L N))
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e)))
    (hb₀ : ∀ j,0<b₀ j) (hFs : ∀ b∈Fs,∀ j,0<b j)
    (hht : ∀ j,0<ht N j)
    (hratio : ∀ e,∃ d : ℤ,height (ht N) (D.added e)=
      height (ht N) (block D.index D.tail (D.owner e))*((primorial w:ℤ)^w*d))
    (hlarge : ∀ v∈slots D s r hs Fs q₀ b₀,(∑ e,|v e|)*L N<(Xp:ℤ)) (τ : ℝ) :
    let C:=heightCoeff D q₀ ht
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    cellRatio Xp (primorial w) (M N) (J N) z.2 hW hXp
      {k | ((d.atTime N).localModel z).modelSuccess (coord D) (k:ℤ) s r hs
        (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ} ≤
    conditionalSlotMass X Xp (primorial w) (M N) (J N) hW hX hXp
      (rawSlot D s r hs Fs q₀ b₀ L ht N)
      (pivotSet D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N τ) z
 := by
  dsimp only
  let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L (heightCoeff D q₀ ht) g₀ x₀ obs₀
  let S : Set ℕ:={k | ((d.atTime N).localModel z).modelSuccess (coord D) (k:ℤ) s r hs
    (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ}
  let slot:=rawSlot D s r hs Fs q₀ b₀ L ht N
  let A:=pivotSet D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N τ
  let f:=MicrocellFibers.point (M N) (J N*(z.2/(M N*J N))) (z.2%M N)
  let ν:Measure ℕ:=(law Xp (primorial w) hW hXp:Measure ℕ)
  change cellRatio Xp (primorial w) (M N) (J N) z.2 hW hXp S ≤
    conditionalSlotMass X Xp (primorial w) (M N) (J N) hW hX hXp slot A z
  rw [conditional_slot_source_ratio X Xp (primorial w) (M N) (J N) hW hX hXp hM hJ z hz slot A]
  unfold cellRatio
  apply div_le_div_of_nonneg_right _ measureReal_nonneg
  change ν.real ((f '' S)∩(sourceCell (M N) (J N) z.2:Set ℕ)) ≤
    ν.real ((f '' {k | (z.1,f k)∈slotEvent slot A})∩(sourceCell (M N) (J N) z.2:Set ℕ))
  have he : ν.real ((f '' S)∩(sourceCell (M N) (J N) z.2:Set ℕ))=
      ν.real (((f '' S)∩(sourceCell (M N) (J N) z.2:Set ℕ))∩(units Xp (primorial w):Set ℕ)) := by
    apply measureReal_congr
    filter_upwards [law_ae_units Xp (primorial w) hW hXp] with p hp
    exact propext ⟨fun h=>⟨h,hp⟩,fun h=>h.1⟩
  rw [he]
  refine measureReal_mono ?_ (by finiteness)
  rintro p ⟨⟨⟨k,hk,hkp⟩,hcell⟩,hpunit⟩
  refine ⟨⟨k,?_,hkp⟩,hcell⟩
  have hpge : (Xp:ℤ)≤(p:ℤ) := by
    exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hpunit).1).1
  have hpform : (p:ℤ)=firstPivot (M N) (J N) z.2+(M N:ℤ)*(k:ℤ) := by
    rw [←hkp,firstPivot_eq_point]
    simp only [f,MicrocellFibers.point,Nat.cast_add,Nat.cast_mul,mul_zero,add_zero]
  have hread:=source_pivot_reading D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L g₀ x₀ obs₀ ht
    N w z k p hq₀ hQq hw hL hWL hML hu hd hb₀ hFs hht hratio hpform
    (fun v hv=>(hlarge v hv).trans_le hpge) τ
  obtain ⟨v,hv,hpos,hprop⟩:=hread hk
  let vv : {v : Slots D // v∈slots D s r hs Fs q₀ b₀}:=⟨v,hv⟩
  change ∃ j,(f k:ℤ)+slot j z.1∈A z.1
  refine ⟨(Fintype.equivFin _ ) vv,?_⟩
  dsimp only [slot,rawSlot]
  rw [Equiv.symm_apply_apply,hkp]
  exact ⟨hpos,hprop⟩

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
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
open MeasureTheory SourcePivotExtension RawHarmonicProbability ProductExposureLaw
 

def slotBudget : ℤ := ∑ v∈slots D s r hs Fs q₀ b₀,∑ e,|v e|
 

theorem source_actual_extension (N w : ℕ) (X : Fin a→ℕ) (Xp : ℕ)
    (hW : 0<primorial w) (hX : ∀ j,4*primorial w≤X j) (hXp : 4*primorial w≤Xp)
    (hM : 0<M N) (hJ : 0<J N)
    (hq₀ : 0<q₀) (hQq : terminalDenom D s r hs Fs b₀∣q₀) (hw : q₀+1≤w)
    (hL : 0<L N) (hsm : RoughScales.Smooth w (L N))
    (hWL : (primorial w:ℤ)∣L N) (hML : (M N:ℤ)∣L N)
    (hd : ∀ e,Disjoint (D.added e) (D.tail (D.owner e)))
    (hb₀ : ∀ j,0<b₀ j) (hFs : ∀ b∈Fs,∀ j,0<b j)
    (hht : ∀ j,0<ht N j)
    (hratio : ∀ e,∃ d : ℤ,height (ht N) (D.added e)=
      height (ht N) (block D.index D.tail (D.owner e))*((primorial w:ℤ)^w*d))
    (hlarge : slotBudget D s r hs Fs q₀ b₀*L N<(Xp:ℤ))
    (τ c : ℝ) (hc : 0≤c) (E : Set (Fin a→ℕ)) :
    let C:=heightCoeff D q₀ ht
    let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L C g₀ x₀ obs₀
    let μ:=jointLaw X Xp (primorial w) hW hX hXp
    c*(μ.real {z | z.1∈E}-μ.real {z |
        cellRatio Xp (primorial w) (M N) (J N) z.2 hW hXp
          {k | ((d.atTime N).localModel z).modelSuccess (coord D) (k:ℤ) s r hs
            (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ}≤c}) ≤
      (slotCount D s r hs Fs q₀ b₀:ℝ)*
        (μ.real {z | z.1∈E ∧ pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N z.1 z.2 τ}+
          4*(primorial w:ℝ)*(slotBudget D s r hs Fs q₀ b₀:ℝ)*(L N:ℝ)/Xp)
 := by
  dsimp only
  let d:=family D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L (heightCoeff D q₀ ht) g₀ x₀ obs₀
  let μ:=jointLaw X Xp (primorial w) hW hX hXp
  let slot:=rawSlot D s r hs Fs q₀ b₀ L ht N
  let A:=pivotSet D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N τ
  let B:ℝ:=(slotBudget D s r hs Fs q₀ b₀:ℝ)*(L N:ℝ)
  let bad : Set ((Fin a→ℕ)×ℕ):={z |
    cellRatio Xp (primorial w) (M N) (J N) z.2 hW hXp
      {k | ((d.atTime N).localModel z).modelSuccess (coord D) (k:ℤ) s r hs
        (FiniteModelSlots.formula D s r hs Fs q₀ b₀) Fs q₀ b₀ τ}≤c}
  have hbudget0 : 0 ≤ slotBudget D s r hs Fs q₀ b₀:=
    Finset.sum_nonneg (fun v hv=>Finset.sum_nonneg (fun e he=>abs_nonneg _))
  have hbudget (v : Slots D) (hv : v∈slots D s r hs Fs q₀ b₀) :
      (∑ e,|v e|) ≤ slotBudget D s r hs Fs q₀ b₀:= by
    unfold slotBudget
    exact Finset.single_le_sum (f:=fun v : Slots D=>∑ e,|v e|)
      (fun v hv=>Finset.sum_nonneg (fun e he=>abs_nonneg (v e))) hv
  have hB : 0≤B:=mul_nonneg (by exact_mod_cast hbudget0) (by exact_mod_cast hL.le)
  have hunits (y : Fin a→ℕ) (hy : y∈outsideDomain X (primorial w)) (j : Fin a) :
      IsCoprime (y j:ℤ) (L N) := by
    have hj:=(Finset.mem_filter.mp (Fintype.mem_piFinset.mp hy j)).2
    apply (RoughScales.coprime_smooth_rough hsm _).symm
    apply (RoughScales.rough_iff_coprime w (y j:ℤ)).mpr
    simpa only [Int.natAbs_natCast] using hj.symm
  have ht₁:=(source_terminal_arithmetic D (outcomeScales D s r hs Fs b₀)).choose_spec.2
    q₀ hq₀ hQq w hw 1 (by simp [outcomeScales]) (by intro j;exact zero_lt_one)
    (ht N) (fun _=>1) hht hratio
  have hcoeff : ∀ e,(primorial w:ℤ)∣heightCoeff D q₀ ht N e := by
    intro e
    simpa [heightCoeff,coefficient,height] using ht₁.1 e
  have hslot : ∀ v y,y∈outsideDomain X (primorial w) →
      (primorial w:ℤ)∣slot v y ∧ |(slot v y:ℝ)|≤B := by
    intro i y hy
    let v:=((Fintype.equivFin {v : Slots D // v∈slots D s r hs Fs q₀ b₀}).symm i).val
    have hv : v∈slots D s r hs Fs q₀ b₀:=((Fintype.equivFin _).symm i).property
    change (primorial w:ℤ)∣slotValue D (L N) (heightCoeff D q₀ ht N) (fun j=>(y j:ℤ)) v ∧ _
    by_cases hn : Nonempty (Fin D.targets)
    · let t:=Classical.choice hn
      have hh:=(source_exposure_slots D (L N) (primorial w:ℤ) hL hWL (heightCoeff D q₀ ht N) hcoeff
        (fun j=>(y j:ℤ)) (fun j=>(y j:ℤ)) (hunits y hy) t
        (fun j hj=>Int.ModEq.refl _) (fun j hj=>rfl) hd).2.2 v
      refine ⟨hh.2.1,?_⟩
      have hbi:=hh.2.2.trans (mul_le_mul_of_nonneg_right (hbudget v hv) hL.le)
      change |(slotValue D (L N) (heightCoeff D q₀ ht N) (fun j=>(y j:ℤ)) v:ℝ)|≤_
      dsimp only [B]
      exact_mod_cast hbi
    · let : IsEmpty (Fin D.pairs):=⟨fun e=>hn ⟨D.owner e⟩⟩
      simp only [slotValue,Finset.univ_eq_empty,Finset.sum_empty,dvd_zero,true_and]
      change |((∑ e,v e*rValue D (L N) (heightCoeff D q₀ ht N) (fun j=>(y j:ℤ)) e:ℤ):ℝ)|≤B
      simpa using hB
  have ho : ∀ᵐ z ∂μ,z.1∈outsideDomain X (primorial w) :=
    (measurePreserving_fst (μ:=outsideLaw X (primorial w) hW hX)
      (ν:=(law Xp (primorial w) hW hXp:Measure ℕ))).quasiMeasurePreserving.ae
      (outside_ae_domain X (primorial w) hW hX)
  have hbad : μ.real {z | conditionalSlotMass X Xp (primorial w) (M N) (J N) hW hX hXp slot A z≤c}≤μ.real bad := by
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [ho] with z hz
    intro hpost
    have hh:=source_posterior_domination D s r hs Fs q₀ b₀ G₀ Γ₀ M J R H L g₀ x₀ obs₀ ht
      N w z X Xp hW hX hXp hz hM hJ hq₀ hQq hw hL hWL hML (hunits z.1 hz) hd hb₀ hFs hht hratio
      (fun v hv=>(mul_le_mul_of_nonneg_right (hbudget v hv) hL.le).trans_lt hlarge) τ
    exact hh.trans hpost
  have hh:=raw_pivot_extension X Xp (primorial w) (M N) (J N) hW hX hXp E A slot B c hB hc hslot
  change c*(μ.real {z | z.1∈E}-μ.real bad)≤_
  apply le_trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hbad _) hc)
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp : μ.real {z | z.1∈E ∧ (z.2:ℤ)∈A z.1}≤
      μ.real {z | z.1∈E ∧ pivotProperty D s r hs Fs b₀ G₀ Γ₀ M H g₀ x₀ obs₀ ht N z.1 z.2 τ} := by
    refine measureReal_mono ?_ (by finiteness)
    rintro z ⟨hz,hp⟩
    exact ⟨hz,hp.2⟩
  have he : 4*(primorial w:ℝ)*B/Xp=4*(primorial w:ℝ)*(slotBudget D s r hs Fs q₀ b₀:ℝ)*(L N:ℝ)/Xp := by
    dsimp [B]
    ring
  rw [he]
  exact add_le_add hp le_rfl

end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily

end
end

end OAI
