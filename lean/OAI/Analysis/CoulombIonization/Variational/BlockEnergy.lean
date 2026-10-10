import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.BlockWedge

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory
open scoped BigOperators

lemma tensor_pair_right {N M : ℕ} (ψ : FormVector N) (φ : FormVector M)
    (s : Spins N) (t : Spins M) (i j : Fin M) :
    (∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inr i))-z (finSumFinEquiv (Sum.inr j))‖) =
      (∫ x, ‖ψ.value s x‖^2)*(∫ y, ‖φ.value t y‖^2 / ‖y i-y j‖) := by
  change (∫ z, ‖ψ.value (leftList (joinLists s t)) (leftList z) *
    φ.value (rightList (joinLists s t)) (rightList z)‖^2 / ‖rightList z i-rightList z j‖) = _
  simp only [leftList_join,rightList_join,norm_mul,mul_pow,mul_div_assoc]
  exact integral_product_join (N := N) (M := M) (fun x => ‖ψ.value s x‖^2)
    (fun y => ‖φ.value t y‖^2 / ‖y i-y j‖)

lemma sum_pair_blocks {N M : ℕ} (f : Fin (N+M) → Fin (N+M) → ℝ) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then
        f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) else 0) +
      (∑ i : Fin M, ∑ j : Fin M, if i < j then
        f (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) else 0) +
      ∑ i : Fin N, ∑ j : Fin M,
        f (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) := by
  have he (g : Fin (N+M) → ℝ) : (∑ i, g i) =
      (∑ i : Fin N, g (finSumFinEquiv (Sum.inl i))) +
      ∑ i : Fin M, g (finSumFinEquiv (Sum.inr i)) := by
    rw [← Equiv.sum_comp finSumFinEquiv,Fintype.sum_sum_type]
  rw [he]
  simp_rw [he,Finset.sum_add_distrib]
  have hlr (i : Fin N) (j : Fin M) : finSumFinEquiv (Sum.inl i) < finSumFinEquiv (Sum.inr j) := by
    simp only [finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,Fin.lt_def,
      Fin.val_castAdd,Fin.val_natAdd]
    omega
  have hrl (i : Fin M) (j : Fin N) : ¬finSumFinEquiv (Sum.inr i) < finSumFinEquiv (Sum.inl j) :=
    not_lt_of_ge (hlr j i).le
  have hll (i j : Fin N) : (finSumFinEquiv : Fin N ⊕ Fin M ≃ Fin (N+M)) (Sum.inl i) < finSumFinEquiv (Sum.inl j) ↔ i < j := by
    simp only [finSumFinEquiv_apply_left,Fin.lt_def,Fin.val_castAdd]
  have hrr (i j : Fin M) : (finSumFinEquiv : Fin N ⊕ Fin M ≃ Fin (N+M)) (Sum.inr i) < finSumFinEquiv (Sum.inr j) ↔ i < j := by
    simp
  simp_rw [hlr,hrl,hll,hrr,ite_true,ite_false,Finset.sum_const_zero,zero_add]
  ring

def blockTensorCross {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) : ℝ :=
  ∑ s : Spins N, ∑ t : Spins M, ∑ i : Fin N, ∑ j : Fin M,
    ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖

lemma formRepulsion_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) :
    formRepulsion (tensorForm ψ φ) = formRepulsion ψ * formMass φ +
      formMass ψ * formRepulsion φ + blockTensorCross ψ φ := by
  unfold formRepulsion blockTensorCross formMass
  rw [← sum_spin_join]
  have he (s : Spins N) (t : Spins M) :
      (∑ i : Fin (N+M), ∑ j : Fin (N+M), if i < j then
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 / ‖z i-z j‖ else 0) =
      (∑ i : Fin N, ∑ j : Fin N, if i < j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0)*
        (∫ y, ‖φ.value t y‖^2) +
      (∫ x, ‖ψ.value s x‖^2)*
        (∑ i : Fin M, ∑ j : Fin M, if i < j then ∫ y, ‖φ.value t y‖^2 / ‖y i-y j‖ else 0) +
      ∑ i : Fin N, ∑ j : Fin M,
        ∫ z, ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
          ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖ := by
    rw [sum_pair_blocks]
    simp only [tensor_pair_left,tensor_pair_right,Finset.sum_mul,Finset.mul_sum,
      ite_mul,mul_ite,zero_mul,mul_zero]
  simp_rw [he,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

lemma formEnergy_tensor {N M : ℕ} (ψ : FormVector N) (φ : FormVector M) (Z : ℝ) :
    formEnergy Z (tensorForm ψ φ) = formEnergy Z ψ * formMass φ +
      formMass ψ * formEnergy Z φ + blockTensorCross ψ φ := by
  rw [formEnergy_parts,formKinetic_tensor,formNuclear_tensor,formRepulsion_tensor,
    formEnergy_parts,formEnergy_parts]
  ring

theorem energy_le_block_insertion {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) {ψ : FormVector N} {φ : FormVector M}
    (hψ : FormAdmissible ψ) (hφ : FormAdmissible φ) (A : Set Space)
    (hc : ∀ x i, x i ∉ A → FormZeroAt ψ x)
    (he : ∀ x i, x i ∈ A → FormZeroAt φ x) :
    energy Z (N+M) ≤ formEnergy Z ψ + formEnergy Z φ + blockTensorCross ψ φ := by
  obtain ⟨F,hF,hE⟩ := normalized_block_wedge_trial hψ hφ A hc he Z
  have hv := energy_le_form hZ hF
  rw [hE,formEnergy_tensor,formMass,formMass,hψ.2.2.2.2.1,hφ.2.2.2.2.1,mul_one,one_mul] at hv
  exact hv

open MeasureTheory
open scoped BigOperators

lemma tensor_cross_pair_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    Integrable (fun z : Configuration (N+M) =>
      ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖) := by
  apply (hψ.tensor hφ).pair_integrable
  exact fun h => Sum.inl_ne_inr (finSumFinEquiv.injective h)

lemma tensor_cross_pair_left_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 *
      ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖) := by
  have hi := integrable_join (N := N) (M := M) (tensor_cross_pair_integrable hψ hφ s t i j)
  rw [Measure.volume_eq_prod] at hi
  have ht := hi.integral_prod_left
  simpa only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul] using ht

lemma tensor_cross_pair {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ)
    (s : Spins N) (t : Spins M) (i : Fin N) (j : Fin M) :
    (∫ z : Configuration (N+M), ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
      ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖) =
      ∫ x : Configuration N, ‖ψ.value s x‖^2 *
        ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖ := by
  have hi := tensor_cross_pair_integrable hψ hφ s t i j
  have hj := integrable_join (N := N) (M := M) hi
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding (fun z : Configuration (N+M) =>
      ‖(tensorForm ψ φ).value (joinLists s t) z‖^2 /
        ‖z (finSumFinEquiv (Sum.inl i))-z (finSumFinEquiv (Sum.inr j))‖)
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  rw [← he,integral_prod _ hj]
  simp only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul]

lemma blockCross_inner_integrable {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) (s : Spins N) (i : Fin N) :
    Integrable (fun x : Configuration N => ‖ψ.value s x‖^2 *
      ∑ t : Spins M, ∑ j : Fin M, ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ (fun t _ => integrable_finsetSum _ (fun j _ =>
    tensor_cross_pair_left_integrable hψ hφ s t i j))

lemma blockTensorCross_fubini {N M : ℕ} {ψ : FormVector N} {φ : FormVector M}
    (hψ : SobolevVector ψ) (hφ : SobolevVector φ) :
    blockTensorCross ψ φ = ∑ s : Spins N, ∑ i : Fin N,
      ∫ x : Configuration N, ‖ψ.value s x‖^2 *
        ∑ t : Spins M, ∑ j : Fin M, ∫ y : Configuration M, ‖φ.value t y‖^2 / ‖x i-y j‖ := by
  unfold blockTensorCross
  simp_rw [tensor_cross_pair hψ hφ]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun j _ =>
    tensor_cross_pair_left_integrable hψ hφ s t i j))]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum _ (fun j _ => tensor_cross_pair_left_integrable hψ hφ s t i j)]

end CoulombAtom

end

end OAI
