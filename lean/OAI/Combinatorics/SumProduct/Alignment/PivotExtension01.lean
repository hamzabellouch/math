import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.HarmonicTranslation01
import OAI.Combinatorics.SumProduct.Alignment.ProductExposure04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section

noncomputable section
namespace SourceJointShift
open MeasureTheory Filter Topology ProductExposureLaw RawHarmonicProbability
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

private lemma raw_eval_nat (X W : ℕ) (f : ℤ→ℝ) :
    HarmonicTranslation.eval (HarmonicTranslation.raw X W) f =
      ∑ n∈Finset.Ico X (X^2),if W.Coprime n then (n:ℝ)⁻¹*f (n:ℤ) else 0 := by
  have hs : (HarmonicTranslation.raw X W).support ⊆ Finset.Ico (X:ℤ) ((X:ℤ)^2) := by
    intro n hn
    have hh:=Finsupp.mem_support_iff.mp hn
    rw [HarmonicTranslation.raw_apply] at hh
    split_ifs at hh with h
    · exact Finset.mem_Ico.mpr ⟨h.1,h.2.1⟩
    · exact (hh rfl).elim
  rw [HarmonicTranslation.eval,(HarmonicTranslation.raw X W).sum_of_support_subset hs
    (fun n a=>a*f n) (by simp)]
  symm
  apply Finset.sum_bij (fun (n:ℕ) _=>(n:ℤ))
  · intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn1,hn2⟩
    exact Finset.mem_Ico.mpr ⟨by exact_mod_cast hn1,by exact_mod_cast hn2⟩
  · intro n hn k hk he
    exact_mod_cast he
  · intro z hz
    rcases Finset.mem_Ico.mp hz with ⟨hz1,hz2⟩
    have hz0 : 0≤z := (Int.natCast_nonneg X).trans hz1
    refine ⟨z.toNat,Finset.mem_Ico.mpr ⟨?_,?_⟩,Int.toNat_of_nonneg hz0⟩
    · have ht : (X:ℤ)≤(z.toNat:ℤ) := by rwa [Int.toNat_of_nonneg hz0]
      exact_mod_cast ht
    · apply (Int.toNat_lt hz0).mpr
      exact_mod_cast hz2
  · intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn1,hn2⟩
    have h1 : (X:ℤ)≤n := by exact_mod_cast hn1
    have h2 : (n:ℤ)<(X:ℤ)^2 := by exact_mod_cast hn2
    simp only [HarmonicTranslation.raw_apply,h1,h2,true_and,Int.isCoprime_iff_nat_coprime,
      Int.natAbs_natCast,Int.cast_natCast,Nat.coprime_comm (n:=n) (m:=W)]
    split_ifs <;> simp

private lemma raw_mass_nat (X W : ℕ) :
    HarmonicTranslation.mass (HarmonicTranslation.raw X W)=
      DyadicHarmonicBoundary.mass X (X^2) W := by
  have hh:=raw_eval_nat X W (fun _=>1)
  simpa [HarmonicTranslation.eval,HarmonicTranslation.mass,DyadicHarmonicBoundary.mass] using hh

private lemma law_eval_nat (X W : ℕ) (hW : 0<W) (hX : 4*W≤X) (A : Set ℤ) :
    HarmonicTranslation.eval (HarmonicTranslation.law X W) (fun n=>if n∈A then 1 else 0)=
      (law X W hW hX:Measure ℕ).real {p | (p:ℤ)∈A} := by
  rw [law_apply,HarmonicTranslation.law,HarmonicTranslation.eval,Finsupp.sum_smul_index (by simp)]
  have he : (HarmonicTranslation.raw X W).sum
      (fun n a=>(HarmonicTranslation.mass (HarmonicTranslation.raw X W))⁻¹ * a * (if n∈A then 1 else 0)) =
      (HarmonicTranslation.mass (HarmonicTranslation.raw X W))⁻¹ *
        HarmonicTranslation.eval (HarmonicTranslation.raw X W) (fun n=>if n∈A then 1 else 0) := by
    simp only [HarmonicTranslation.eval,Finsupp.sum,mul_assoc,Finset.mul_sum]
  rw [he,raw_eval_nat,raw_mass_nat,←div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Set.mem_ofPred_eq]
  split_ifs <;> simp_all

private lemma law_shift_event (X W : ℕ) (hW : 0<W) (hX : 4*W≤X)
    (h : ℤ) (hh : (W:ℤ)∣h) (A : Set ℤ) :
    |(law X W hW hX:Measure ℕ).real {p | (p:ℤ)+h∈A}-
      (law X W hW hX:Measure ℕ).real {p | (p:ℤ)∈A}| ≤4*(W:ℝ)*|(h:ℝ)|/X := by
  have hfirst:=law_eval_nat X W hW hX {n | n+h∈A}
  simp only [Set.mem_ofPred_eq] at hfirst
  rw [←hfirst,←law_eval_nat X W hW hX A]
  change |HarmonicTranslation.eval (HarmonicTranslation.law X W) (fun n=>if n+h∈A then 1 else 0)-
    HarmonicTranslation.eval (HarmonicTranslation.law X W) (fun n=>if n∈A then 1 else 0)|≤_
  rw [←HarmonicTranslation.eval_shift h (HarmonicTranslation.law X W) (fun n=>if n∈A then 1 else 0),
    ←HarmonicTranslation.eval_sub]
  have hb:=HarmonicTranslation.eval_bound
    (HarmonicTranslation.shift h (HarmonicTranslation.law X W)-HarmonicTranslation.law X W)
    (fun n=>if n∈A then 1 else 0) (B:=1) (by intro n; split_ifs <;> norm_num)
  rw [mul_one] at hb
  exact hb.trans (HarmonicTranslation.law_translation hW (by omega) hh)

private lemma joint_pivot_disintegration {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (E : Set ((Fin m→ℕ)×ℕ)) :
    (jointLaw X Xp W hW hX hXp).real E=
      ∑ y∈outsideDomain X W,(outsideLaw X W hW hX).real {y} *
        (law Xp W hW hXp:Measure ℕ).real {p | (y,p)∈E} := by
  change ((outsideLaw X W hW hX).prod (law Xp W hW hXp:Measure ℕ)).real E=_
  rw [measureReal_def,Measure.prod_apply MeasurableSet.of_discrete]
  conv_lhs => rw [←Measure.restrict_eq_self_of_ae_mem (outside_ae_domain X W hW hX)]
  rw [lintegral_finset,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y hy
    rw [ENNReal.toReal_mul,mul_comm]
    rfl
  · intro y hy
    exact ENNReal.mul_ne_top (by finiteness) (by finiteness)
 

theorem raw_joint_shift {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (E : Set (Fin m→ℕ)) (A : (Fin m→ℕ)→Set ℤ) (slot : (Fin m→ℕ)→ℤ)
    (B : ℝ) (hB : 0≤B)
    (hslot : ∀ y∈outsideDomain X W,(W:ℤ)∣slot y ∧ |(slot y:ℝ)|≤B) :
    |(jointLaw X Xp W hW hX hXp).real {z | z.1∈E ∧ (z.2:ℤ)+slot z.1∈A z.1} -
      (jointLaw X Xp W hW hX hXp).real {z | z.1∈E ∧ (z.2:ℤ)∈A z.1}| ≤
      4*(W:ℝ)*B/Xp
 := by
  rw [joint_pivot_disintegration,joint_pivot_disintegration,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ y∈outsideDomain X W,|(outsideLaw X W hW hX).real {y} *
        (law Xp W hW hXp:Measure ℕ).real {p | y∈E ∧ (p:ℤ)+slot y∈A y}-
        (outsideLaw X W hW hX).real {y} *
        (law Xp W hW hXp:Measure ℕ).real {p | y∈E ∧ (p:ℤ)∈A y}| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y∈outsideDomain X W,(outsideLaw X W hW hX).real {y} * (4*(W:ℝ)*B/Xp) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [←mul_sub,abs_mul,abs_of_nonneg measureReal_nonneg]
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      by_cases hey : y∈E
      · simp only [hey,true_and]
        apply (law_shift_event Xp W hW hXp (slot y) (hslot y hy).1 (A y)).trans
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hslot y hy).2 (by positivity)) (by positivity)
      · simp only [hey,false_and,Set.ofPred_false,measureReal_empty,sub_self,abs_zero]
        positivity
    _ = _ := by rw [←Finset.sum_mul,outside_weights_sum,one_mul]

end SourceJointShift
end

noncomputable section
namespace SourcePivotExtension
open MeasureTheory ProductExposureLaw ProductExposureLabels RoughFaceShift RawHarmonicProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable
 
def conditioningLabel {m : ℕ} (M J : ℕ) (z : (Fin m→ℕ)×ℕ) :=
  (z.1,(z.2/(M*J),z.2%M))
def conditioningCell {m : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ) (z : (Fin m→ℕ)×ℕ) : Finset ((Fin m→ℕ)×ℕ) :=
  (fullDomain X Xp W).filter (fun u=>conditioningLabel M J u=conditioningLabel M J z)
def slotEvent {m V : ℕ} (slot : Fin V→(Fin m→ℕ)→ℤ) (A : (Fin m→ℕ)→Set ℤ) : Set ((Fin m→ℕ)×ℕ) :=
  {z | ∃ v,(z.2:ℤ)+slot v z.1∈A z.1}
 

def conditionalSlotMass {m V : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (slot : Fin V→(Fin m→ℕ)→ℤ) (A : (Fin m→ℕ)→Set ℤ) (z : (Fin m→ℕ)×ℕ) : ℝ :=
  (jointLaw X Xp W hW hX hXp).real (slotEvent slot A ∩ (conditioningCell X Xp W M J z:Set _)) /
    (jointLaw X Xp W hW hX hXp).real (conditioningCell X Xp W M J z:Set _)

private lemma finite_real {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : Finset α) (A : Set α) :
    μ.real (A∩(S:Set α))=∑ x∈S,if x∈A then μ.real {x} else 0 := by
  classical
  have he : A∩(S:Set α)=(S.filter (fun x=>x∈A):Set α) := by ext x; simp [and_comm]
  rw [he,←sum_measureReal_singleton,Finset.sum_filter]

private lemma finite_ratio_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (w : α→ℝ) (hw : ∀ x∈S,0≤w x) (π : α→β)
    (E : Set β) (A : Set α) (c : ℝ) (hc : 0≤c) :
    c*((∑ x∈S,if π x∈E then w x else 0)-
      ∑ x∈S,if (∑ y∈S.filter (fun y=>π y=π x),if y∈A then w y else 0)/
        (∑ y∈S.filter (fun y=>π y=π x),w y)≤c then w x else 0) ≤
      ∑ x∈S,if π x∈E ∧ x∈A then w x else 0 := by
  classical
  let d (i : β) := ∑ y∈S.filter (fun y=>π y=i),w y
  let n (i : β) := ∑ y∈S.filter (fun y=>π y=i),if y∈A then w y else 0
  let G : Set β := {i | i∈E ∧ c<n i/d i}
  let T := (S.image π).filter (·∈G)
  have hf : S.filter (fun x=>π x∈T)=S.filter (fun x=>π x∈G) := by
    ext x
    simp only [Finset.mem_filter,T]
    constructor
    · exact fun h=>⟨h.1,h.2.2⟩
    · exact fun h=>⟨h.1,Finset.mem_image_of_mem π h.1,h.2⟩
  have hs : c*(∑ x∈S.filter (fun x=>π x∈G),w x) ≤
      ∑ x∈S,if π x∈E ∧ x∈A then w x else 0 := by
    calc
      _ = ∑ i∈T,c*d i := by rw [←Finset.mul_sum,Finset.sum_fiberwise_eq_sum_filter,hf]
      _ ≤ ∑ i∈T,∑ x∈S.filter (fun x=>π x=i),if π x∈E ∧ x∈A then w x else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        have hg : i∈E ∧ c<n i/d i := (Finset.mem_filter.mp hi).2
        have hd : 0≤d i := Finset.sum_nonneg (fun y hy=>hw y (Finset.mem_filter.mp hy).1)
        have hn : 0≤n i := Finset.sum_nonneg (by intro y hy; split_ifs; exact hw y (Finset.mem_filter.mp hy).1; rfl)
        have hh : c*d i≤n i := by
          rcases eq_or_lt_of_le hd with h0|h0
          · rw [←h0,mul_zero]; exact hn
          · exact le_of_lt ((lt_div_iff₀ h0).mp hg.2)
        apply hh.trans_eq
        apply Finset.sum_congr rfl
        intro x hx
        simp only [(Finset.mem_filter.mp hx).2,hg.1,true_and]
      _ = ∑ x∈S.filter (fun x=>π x∈G),if π x∈E ∧ x∈A then w x else 0 := by
        rw [Finset.sum_fiberwise_eq_sum_filter,hf]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro x hx _
        split_ifs
        · exact hw x hx
        · rfl
  apply le_trans ?_ hs
  apply mul_le_mul_of_nonneg_left _ hc
  rw [Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro x hx
  change (if π x∈E then w x else 0)-(if n (π x)/d (π x)≤c then w x else 0) ≤
    if π x∈G then w x else 0
  by_cases he : π x∈E <;> by_cases hb : n (π x)/d (π x)≤c
  · simp [he,hb,G,not_lt.mpr hb]
  · simp [he,hb,G,lt_of_not_ge hb]
  · simp [he,hb,G,hw x hx]
  · simp [he,hb,G]

private lemma support_ae {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) :
    ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z∈fullDomain X Xp W := by
  have ho : ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z.1∈outsideDomain X W :=
    (measurePreserving_fst (μ:=outsideLaw X W hW hX) (ν:=(law Xp W hW hXp:Measure ℕ))).quasiMeasurePreserving.ae
      (outside_ae_domain X W hW hX)
  have hp : ∀ᵐ z ∂jointLaw X Xp W hW hX hXp,z.2∈units Xp W :=
    (measurePreserving_snd (μ:=outsideLaw X W hW hX) (ν:=(law Xp W hW hXp:Measure ℕ))).quasiMeasurePreserving.ae
      (law_ae_units Xp W hW hXp)
  filter_upwards [ho,hp] with z ho hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ho,(Finset.mem_filter.mp hp).1⟩,(Finset.mem_filter.mp hp).2⟩

private lemma joint_real {m : ℕ} (X : Fin m→ℕ) (Xp W : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp) (A : Set ((Fin m→ℕ)×ℕ)) :
    (jointLaw X Xp W hW hX hXp).real A=
      ∑ z∈fullDomain X Xp W,if z∈A then (jointLaw X Xp W hW hX hXp).real {z} else 0 := by
  rw [←finite_real]
  apply measureReal_congr
  filter_upwards [support_ae X Xp W hW hX hXp] with z hz
  exact propext ⟨fun h=>⟨h,hz⟩,fun h=>h.1⟩

private lemma conditional_mass_sum {m V : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (slot : Fin V→(Fin m→ℕ)→ℤ) (A : (Fin m→ℕ)→Set ℤ) (z : (Fin m→ℕ)×ℕ) :
    conditionalSlotMass X Xp W M J hW hX hXp slot A z=
      (∑ y∈(fullDomain X Xp W).filter (fun y=>conditioningLabel M J y=conditioningLabel M J z),
        if y∈slotEvent slot A then (jointLaw X Xp W hW hX hXp).real {y} else 0)/
      (∑ y∈(fullDomain X Xp W).filter (fun y=>conditioningLabel M J y=conditioningLabel M J z),
        (jointLaw X Xp W hW hX hXp).real {y}) := by
  unfold conditionalSlotMass
  rw [finite_real,←sum_measureReal_singleton]
  rfl

private lemma conditional_extension {m V : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (E : Set (Fin m→ℕ)) (A : (Fin m→ℕ)→Set ℤ)
    (slot : Fin V→(Fin m→ℕ)→ℤ) (c : ℝ) (hc : 0≤c) :
    c*((jointLaw X Xp W hW hX hXp).real {z | z.1∈E} -
       (jointLaw X Xp W hW hX hXp).real {z | conditionalSlotMass X Xp W M J hW hX hXp slot A z≤c}) ≤
      (jointLaw X Xp W hW hX hXp).real {z | z.1∈E ∧ z∈slotEvent slot A} := by
  have hh:=finite_ratio_bound (fullDomain X Xp W)
    (fun z=>(jointLaw X Xp W hW hX hXp).real {z}) (fun _ _=>measureReal_nonneg)
    (conditioningLabel M J) {i | i.1∈E} (slotEvent slot A) c hc
  rw [joint_real X Xp W hW hX hXp,joint_real X Xp W hW hX hXp,
    joint_real X Xp W hW hX hXp]
  simp only [Set.mem_ofPred_eq,conditional_mass_sum]
  simp only [Set.mem_ofPred_eq,conditioningLabel] at hh
  apply hh.trans_eq
  apply Finset.sum_congr rfl
  intro point _
  exact (ite_eq_ite _ _ _).mpr trivial

 

theorem raw_pivot_extension {m V : ℕ} (X : Fin m→ℕ) (Xp W M J : ℕ)
    (hW : 0<W) (hX : ∀ j,4*W≤X j) (hXp : 4*W≤Xp)
    (E : Set (Fin m→ℕ)) (A : (Fin m→ℕ)→Set ℤ)
    (slot : Fin V→(Fin m→ℕ)→ℤ) (B c : ℝ) (hB : 0≤B) (hc : 0≤c)
    (hslot : ∀ v y,y∈outsideDomain X W → (W:ℤ)∣slot v y ∧ |(slot v y:ℝ)|≤B) :
    c*((jointLaw X Xp W hW hX hXp).real {z | z.1∈E} -
       (jointLaw X Xp W hW hX hXp).real {z | conditionalSlotMass X Xp W M J hW hX hXp slot A z≤c}) ≤
      (V:ℝ)*((jointLaw X Xp W hW hX hXp).real {z | z.1∈E ∧ (z.2:ℤ)∈A z.1}+
        4*(W:ℝ)*B/Xp)
 := by
  have hh:=conditional_extension X Xp W M J hW hX hXp E A slot c hc
  apply hh.trans
  let F : Fin V→Set ((Fin m→ℕ)×ℕ) := fun v=>{z | z.1∈E ∧ (z.2:ℤ)+slot v z.1∈A z.1}
  have he : {z : (Fin m→ℕ)×ℕ | z.1∈E ∧ z∈slotEvent slot A}=⋃ v,F v := by
    ext z
    simp only [Set.mem_ofPred_eq,slotEvent,Set.mem_iUnion,F]
    aesop
  rw [he]
  calc
    _ ≤ ∑ v,(jointLaw X Xp W hW hX hXp).real (F v) := measureReal_iUnion_fintype_le F
    _ ≤ ∑ _v : Fin V,((jointLaw X Xp W hW hX hXp).real
        {z | z.1∈E ∧ (z.2:ℤ)∈A z.1}+4*(W:ℝ)*B/Xp) := by
      apply Finset.sum_le_sum
      intro v hv
      have h:=(abs_le.mp (SourceJointShift.raw_joint_shift X Xp W hW hX hXp E A (slot v) B hB (hslot v))).2
      change (jointLaw X Xp W hW hX hXp).real {z | z.1∈E ∧ (z.2:ℤ)+slot v z.1∈A z.1}≤_
      linarith
    _ = _ := by simp; ring

end SourcePivotExtension

end
end

end OAI
