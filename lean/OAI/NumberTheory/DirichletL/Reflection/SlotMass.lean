import OAI.NumberTheory.DirichletL.Reflection.SlotChoices

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma inactive_choices_mass (L : σ→Finset (Ideal Eis)) (T : Finset σ) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)=
    ∏ i : {i // i∉T}, ∑ P∈L i.val, (Ideal.absNorm P:ℝ)⁻¹ := by
  simp only [norm_prod,norm_inv,Complex.norm_natCast]
  refine (Fintype.prod_sum (fun (i : {i // i∉T}) (P : L i.val) => (Ideal.absNorm P.val:ℝ)⁻¹)).symm.trans ?_
  apply Finset.prod_congr rfl
  intro i hi
  exact Finset.sum_coe_sort (L i.val) (fun P => (Ideal.absNorm P:ℝ)⁻¹)

lemma inactive_choices_mass_bound (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i) :
    (∑ b : ∀ i : {i // i∉T}, L i.val,
      ‖∏ i : {i // i∉T}, (Ideal.absNorm (b i).val:ℂ)⁻¹‖)≤
      ∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ) := by
  rw [inactive_choices_mass]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa only [one_div] using finite_inverse_norm_sum (L i.val) (H i.val) (hzero i.val) (hH i.val)

theorem original_inactive_choices_energy {κ : Type*}
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (rows : Finset κ)
    (H : σ→ℝ) (hzero : ∀ i, ∀ P∈L i, P≠0)
    (hH : ∀ i, ∀ P∈L i, (Ideal.absNorm P:ℝ)≤H i)
    (f : (∀ i, L i)→κ→ℂ) (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T}, L i.val,
      (∑ k∈rows, ‖∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k‖^2)≤E) :
    (∑ k∈rows, ‖∑ p : ∀ i, L i,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p i).val:ℂ)⁻¹)*f p k‖^2)≤
    (∏ i : {i // i∉T}, 256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  simp_rw [sum_slot_choices L T]
  apply (weighted_finite_row_energy_uniform Finset.univ rows
    (fun b : ∀ i : {i // i∉T}, L i.val => ∏ i, (Ideal.absNorm (b i).val:ℂ)⁻¹)
    (fun b k => ∑ a : ∀ i : T, L i.val, f ((slotChoiceSplit L T).symm (a,b)) k)
    E (fun b hb => hf b)).trans
  apply mul_le_mul_of_nonneg_right _ hE
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun b hb => norm_nonneg _))
    (inactive_choices_mass_bound L T H hzero hH) 2
end
end SevenEighths.InverseReflectedPhase

end OAI
