import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
import OAI.NumberTheory.DirichletL.Reflection.TupleFamily

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def slotChoiceSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∀ i, L i)≃(∀ i : T, L i.val)×(∀ i : {i // i∉T}, L i.val) :=
  Equiv.piEquivPiSubtypeProd (fun i => i∈T) (fun i => L i)

omit [Fintype σ] in
lemma slotChoiceSplit_active (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : T) :
    (slotChoiceSplit L T).symm (a,b) i.val=a i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dite_eq_left i.property]

omit [Fintype σ] in
lemma slotChoiceSplit_inactive (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (i : {i // i∉T}) :
    (slotChoiceSplit L T).symm (a,b) i.val=b i := by
  simp only [slotChoiceSplit,Equiv.piEquivPiSubtypeProd,Equiv.coe_fn_symm_mk,dite_eq_right i.property]

lemma slot_choice_inactive_weight (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (p : ∀ i, L i) :
    (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)=
      ∏ i : {i // i∉T}, (Ideal.absNorm ((slotChoiceSplit L T p).2 i).val:ℂ)⁻¹ := by
  exact Finset.prod_subtype (Finset.univ\T) (fun i => by simp)
    (fun i => (Ideal.absNorm (p i).val:ℂ)⁻¹)

theorem sum_slot_choices (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (H : (∀ i, L i)→ℂ) :
    (∑ p : ∀ i, L i, (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)*H p)=
    ∑ b : ∀ i : {i // i∉T}, L i.val,
      (∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹)*
        ∑ a : ∀ i : T, L i.val, H ((slotChoiceSplit L T).symm (a,b)) := by
  simp_rw [slot_choice_inactive_weight L T]
  rw [← (slotChoiceSplit L T).symm.sum_comp]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]

lemma slot_choice_coprime_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T, L i.val) (b : ∀ i : {i // i∉T}, L i.val) (K : Ideal Eis) :
    IsCoprime K (∏ i, ((slotChoiceSplit L T).symm (a,b) i).val) ↔
      IsCoprime K (∏ i : T, (a i).val) ∧ IsCoprime K (∏ i : {i // i∉T}, (b i).val) := by
  simp only [IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  constructor
  · intro h
    constructor
    · intro i
      simpa only [slotChoiceSplit_active] using h i.val
    · intro i
      simpa only [slotChoiceSplit_inactive] using h i.val
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb ⟨i,hi⟩
end
end SevenEighths.InverseReflectedPhase

end OAI
