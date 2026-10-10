import OAI.NumberTheory.DirichletL.Reflection.InactiveRows
import OAI.NumberTheory.DirichletL.Reflection.MarkedTuples

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

lemma supported_inactive_sum_eq (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis)
    (K : rows) (w : ∀ i,L i→ℂ)
    (f : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ) :
    (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f b)=
    ∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:K.val∈inactiveRowSet rows L T F b then f ⟨b,(Finset.mem_filter.mp hk).2⟩ else 0) := by
  let ok := fun b : ∀ i : {i // i∉T},L i.val =>
    IsCoprime K.val (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  have he := sum_subtype_dite_decidable ok (fun b hb => wt b*f ⟨b,hb⟩)
  change (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,wt b.val*f b)=_
  calc
    _ = ∑ b,if hb:ok b then wt b*f ⟨b,hb⟩ else 0 := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hc : ok b
      · have hk : K.val∈inactiveRowSet rows L T F b := Finset.mem_filter.mpr ⟨K.property,hc⟩
        simp only [dite_eq_left hc,dite_eq_left hk,wt]
      · have hk : K.val∉inactiveRowSet rows L T F b := fun h => hc (Finset.mem_filter.mp h).2
        simp only [dite_eq_right hc,dite_eq_right hk,mul_zero]

theorem supported_inactive_source_energy (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ K : rows,supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T},L i.val,
      (∑ K : inactiveRowSet rows L T F b,
        ‖f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩‖^2)≤E) :
    (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let g := fun (b : ∀ i : {i // i∉T},L i.val) (K : inactiveRowSet rows L T F b) =>
    f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩
  have he := original_inactive_restricted_energy rows L T F H hzero hH w hw g E hE hf
  have hh : (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)=
      ∑ K∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
          (if hk:K∈inactiveRowSet rows L T F b then g b ⟨K,hk⟩ else 0)‖^2 := by
    rw [←Finset.sum_coe_sort rows]
    apply Finset.sum_congr rfl
    intro K hK
    rw [supported_inactive_sum_eq rows L T F K w (f K)]
  exact hh.trans_le he
end
end SevenEighths.InverseReflectedPhase

end OAI
