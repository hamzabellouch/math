import OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
import OAI.NumberTheory.DirichletL.Reflection.SlotMass

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def inactiveRowSet (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (b : ∀ i : {i // i∉T},L i.val) : Finset (Ideal Eis) :=
  rows.filter fun K => IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j

lemma subtype_zero_extension_energy {κ : Type*} [DecidableEq κ]
    (rows small : Finset κ) (hs : small⊆rows) (f : small→ℂ) :
    (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=∑ k : small,‖f k‖^2 := by
  have he : (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=
      ∑ k∈small,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2 := by
    symm
    apply Finset.sum_subset hs
    intro k hk hks
    simp only [dite_eq_right hks,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
  rw [he,←Finset.sum_coe_sort small]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left k.property]

theorem original_inactive_restricted_energy
    (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ b : ∀ i : {i // i∉T},L i.val,inactiveRowSet rows L T F b→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b,(∑ k : inactiveRowSet rows L T F b,‖f b k‖^2)≤E) :
    (∑ k∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0)‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  let g := fun (b : ∀ i : {i // i∉T},L i.val) k =>
    if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0
  have hg (b) : (∑ k∈rows,‖g b k‖^2)≤E := by
    rw [show (∑ k∈rows,‖g b k‖^2)=∑ k : inactiveRowSet rows L T F b,‖f b k‖^2 from
      subtype_zero_extension_energy rows _ (Finset.filter_subset _ _) (f b)]
    exact hf b
  have hm : (∑ b,‖wt b‖)≤∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ) := by
    apply (Finset.sum_le_sum (fun b hb => ?_)).trans (inactive_choices_mass_bound L T H hzero hH)
    change ‖_*_‖≤_
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact slot_coefficient_norm (fun i : {i // i∉T} => L i.val) (fun i => w i.val) (fun i => hw i.val) b
  apply (weighted_finite_row_energy_uniform Finset.univ rows wt g E (fun b hb => hg b)).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => norm_nonneg _)) hm 2) hE
end
end SevenEighths.InverseReflectedPhase

end OAI
