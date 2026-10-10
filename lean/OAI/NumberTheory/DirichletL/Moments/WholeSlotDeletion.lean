import OAI.NumberTheory.DirichletL.Moments.SlotRemoval
import OAI.NumberTheory.DirichletL.Moments.RetainedEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => ActualEisensteinCubic.O

theorem whole_removal {α:Type*} (S:Finset α) (w:α→ℝ) (F κ mesh:ℝ)
    (hF:0≤F) (hκ:0<κ) (hm:0≤mesh)
    (hw:∀i∈S,0≤w i) (hwm:∀i∈S,w i≤mesh) :
    ∃R:Finset α,R⊆S ∧
      (∑i∈R,w i)≤min (∑i∈S,w i) (F/(6*κ)+mesh) ∧
      (R=S ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay⟩:=CenteredMomentSlotRemoval.whole_slot_removal S w mesh κ F hm hκ hF hw hwm
  refine ⟨R,hR,hbound,hpay,?_⟩
  have hh:=mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hκ.le
  have he:κ*(F/(6*κ)+mesh)=F/6+κ*mesh:=by field_simp
  rwa [he] at hh

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

theorem selectedProduct_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂:ℝ) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      (∏i∈R,normalizedSlot η m A z (S i) (β i) t (P i))*
        selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct
  rw [←Finset.prod_sdiff hR]
  ring

theorem selectedProduct_energy_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂ Z κ:ℝ)
    (hZ:0<Z) (w B:α→ℝ) (_hB:∀i∈R,0≤B i)
    (hslot:∀i∈R,‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2≤B i*Z^(κ*w i)) :
    ‖selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((∏i∈R,B i)*Z^(κ*∑i∈R,w i))*
        ‖selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  rw [selectedProduct_remove J R hR,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏i∈R,B i*Z^(κ*w i):=Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot
    _=_:=by rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,Finset.mul_sum]

end SevenEighths.CenteredMomentWholeSlotDeletion

end

end OAI
