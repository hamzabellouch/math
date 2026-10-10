import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.SlaterMeasure

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SpinSpaceIntegrable_scope

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate ContDiff

lemma spinSpace_integrable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {F : (Fin n → SlaterParticle) → E} (hm : Measurable F)
    (hi : ∀ s : Spins n, Integrable (fun x : Configuration n => F (slaterParticles s x))) :
    Integrable F (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  have mp := (spinSpace_measurePreserving n).symm
  apply (mp.integrable_comp_emb
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurableEmbedding).mp
  apply (integrable_prod_iff (hm.comp
    (MeasurableEquiv.arrowProdEquivProdArrow (Fin 2) Space (Fin n)).symm.measurable).aestronglyMeasurable).mpr
  exact ⟨Eventually.of_forall hi, Integrable.of_finite⟩

lemma continuous_slater {α : Type*} [TopologicalSpace α] {n : ℕ}
    {φ : Fin n → α → ℂ} (hφ : ∀ i, Continuous (φ i)) : Continuous (slater φ) := by
  unfold slater slaterRaw slaterTensor
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetProd
  intro i _
  exact (hφ (σ i)).comp (continuous_apply i)

lemma slater_coulomb_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (j k : Fin n) (hjk : j ≠ k) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖(z j).2-(z k).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  apply spinSpace_integrable
  · exact ((continuous_slater (fun i => continuous_prod_of_discrete_left.mpr
      (fun s => (hφ i s).continuous))).measurable.norm.pow_const 2).div
      (((measurable_pi_apply j).snd.sub (measurable_pi_apply k).snd).norm)
  · intro s
    exact (slaterForm_sobolevFermion hφ hc).sobolevVector.pair_integrable s j k hjk

lemma slater_nuclear_integrable {n : ℕ} {φ : Fin n → SlaterParticle → ℂ}
    (hφ : ∀ i s, ContDiff ℝ ∞ (fun x : Space => φ i (s,x)))
    (hc : ∀ i s, HasCompactSupport (fun x : Space => φ i (s,x)))
    (j : Fin n) :
    Integrable (fun z : Fin n → SlaterParticle => ‖slater φ z‖^2 / ‖(z j).2‖)
      (Measure.pi fun _ : Fin n => slaterParticleMeasure) := by
  apply spinSpace_integrable
  · exact ((continuous_slater (fun i => continuous_prod_of_discrete_left.mpr
      (fun s => (hφ i s).continuous))).measurable.norm.pow_const 2).div
      (measurable_pi_apply j).snd.norm
  · intro s
    exact (slaterForm_sobolevFermion hφ hc).sobolevVector.nuclear_integrable s j

end Work_SpinSpaceIntegrable_scope

open MeasureTheory
open scoped BigOperators

lemma sum_ordered_pairs {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then f i j else 0) =
      2 * ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
  have he (i j : Fin n) : (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    by_cases h : i=j
    · subst j; simp
    rcases lt_or_gt_of_ne h with h | h
    · simp only [ite_eq_left h,ite_eq_left (ne_of_lt h),ite_eq_right (not_lt_of_ge h.le),add_zero]
    · simp only [ite_eq_left h,ite_eq_left (ne_of_gt h),ite_eq_right (not_lt_of_ge h.le),zero_add]
  simp_rw [he,Finset.sum_add_distrib]
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  rw [hs]
  ring

lemma formRepulsion_ordered {n : ℕ} (ψ : FormVector n) :
    formRepulsion ψ = (1/2:ℝ) * ∑ s : Spins n, ∑ i : Fin n, ∑ j : Fin n,
      if i ≠ j then ∫ x, ‖ψ.value s x‖^2 / ‖x i-x j‖ else 0 := by
  have he (s : Spins n) := sum_ordered_pairs
    (fun i j : Fin n => ∫ x : Configuration n, ‖ψ.value s x‖^2 / ‖x i-x j‖)
    (fun i j => by simp only [norm_sub_rev])
  simp_rw [he]
  rw [← Finset.mul_sum]
  unfold formRepulsion
  ring

end CoulombAtom

end

end OAI
