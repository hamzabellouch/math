import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
import OAI.NumberTheory.DirichletL.Reflection.OriginalMask

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalSlotChoices :=
  {p : ∀ i,L i // ∀ P : FreePrimeIndex D.movingIdeal Q₀,∀ i,(p i).val≠P.val.val}

def originalSlotSupportEquiv :
    originalSlotChoices D Q₀ L ≃ supportedSlotChoices L ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) where
  toFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mp p.property⟩
  invFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mpr p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl

def originalSlotSplit (T : Finset σ) : originalSlotChoices D Q₀ L ≃
    supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) :=
  (originalSlotSupportEquiv D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood).trans
    (supportedSlotSplit L T ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))

lemma originalSlotSplit_symm_val (T : Finset σ)
    (b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))
    (a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) :
    ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)).val=
      (slotChoiceSplit L T).symm (a.val,b.val) := rfl

theorem original_supported_slot_sum (T : Finset σ)
    (w : ∀ i,L i→ℂ) (H : originalSlotChoices D Q₀ L→ℂ) :
    (∑ p : originalSlotChoices D Q₀ L,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p.val i).val:ℂ)⁻¹)*
        (∏ i,w i (p.val i))*H p)=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
        (∏ i : T,w i.val (a.val i))*
        H ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  rw [←(originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [originalSlotSplit_symm_val,slot_choice_inactive_weight,Equiv.apply_symm_apply,slot_coefficient_split]
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
