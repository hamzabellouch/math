import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.SobolevVector

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
lemma sum_pairs_half {N : ℕ} (f : Fin N → Fin N → ℝ) (hs : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if i < j then f i j else 0) =
      (1/2:ℝ) * ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
  classical
  have he : (∑ i, ∑ j, if i ≠ j then f i j else 0) =
      (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge (le_of_lt h)]
  have hr : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hs j i]
  rw [he, hr]
  ring


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators


def configurationReindex {M N : ℕ} (e : Fin M ≃ Fin N) :
    Configuration M ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => Space) e

@[simp] lemma configurationReindex_apply {M N : ℕ} (e : Fin M ≃ Fin N) (x : Configuration M) :
    configurationReindex e x = x ∘ e.symm := by
  ext i
  simp [configurationReindex, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft]

lemma configurationReindex_preserving {M N : ℕ} (e : Fin M ≃ Fin N) :
    MeasurePreserving (configurationReindex e) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin N => Space) e

lemma configurationReindex_direction {M N : ℕ} (e : Fin M ≃ Fin N)
    (i : Fin M) (a : Fin 3) :
    configurationReindex e (direction i a) = direction (e i) a := by
  rw [configurationReindex_apply]
  ext j k
  by_cases hj : j = e i
  · subst j; simp [direction]
  · have hi : e.symm j ≠ i := fun hh => hj (by rw [← hh, e.apply_symm_apply])
    simp [direction, hj, hi]

def reindexForm {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) : FormVector M where
  value s x := ψ.value (s ∘ e.symm) (x ∘ e.symm)
  gradient s i a x := ψ.gradient (s ∘ e.symm) (e i) a (x ∘ e.symm)

lemma SobolevVector.reindex {M N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (e : Fin M ≃ Fin N) : SobolevVector (reindexForm e ψ) := by
  refine ⟨fun s => ?_, fun s i a => ?_, fun s i a => ?_⟩
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.1 (s ∘ e.symm)).comp_measurePreserving (configurationReindex_preserving e)
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.2.1 (s ∘ e.symm) (e i) a).comp_measurePreserving (configurationReindex_preserving e)
  · simpa only [Function.comp_def, configurationReindex_apply, reindexForm] using
      (hψ.2.2 (s ∘ e.symm) (e i) a).pullback (configurationReindex e)
        (configurationReindex_preserving e) (configurationReindex_direction e i a)

lemma SobolevFermion.reindex {M N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (e : Fin M ≃ Fin N) : SobolevFermion (reindexForm e ψ) := by
  have hr := hψ.sobolevVector.reindex e
  refine ⟨hr.1,hr.2.1,hr.2.2,?_⟩
  intro π s
  have hh := (configurationReindex_preserving e).quasiMeasurePreserving.ae
    (hψ.2.2.2 (e.permCongr π) (s ∘ e.symm))
  filter_upwards [hh] with x hx
  simpa only [configurationReindex_apply, Equiv.Perm.sign_permCongr,
    Function.comp_def, Equiv.permCongr_apply, Equiv.symm_apply_apply, reindexForm] using hx

lemma integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (f : Configuration N → ℝ) :
    (∫ x : Configuration M, f (x ∘ e.symm)) = ∫ x, f x := by
  simpa only [configurationReindex_apply] using (configurationReindex_preserving e).integral_comp
    (configurationReindex e).toHomeomorph.measurableEmbedding f

lemma sum_spin_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (f : Spins N → ℝ) :
    (∑ s : Spins M, f (s ∘ e.symm)) = ∑ s, f s := by
  have he (s : Spins M) : (Equiv.piCongrLeft (fun _ : Fin N => Fin 2) e) s = s ∘ e.symm := by
    ext i
    simp [Equiv.piCongrLeft_apply]
  simpa only [he] using
    Equiv.sum_comp (Equiv.piCongrLeft (fun _ : Fin N => Fin 2) e) f

lemma formMass_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) :
    formMass (reindexForm e ψ) = formMass ψ := by
  unfold formMass
  have h (s : Spins M) : (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 :=
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2)
  simp_rw [h]
  exact sum_spin_reindex e (fun s => ∫ x, ‖ψ.value s x‖ ^ 2)

lemma nuclear_integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N)
    (s : Spins M) (i : Fin M) :
    (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)‖ := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, reindexForm] using
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)‖)

lemma pair_integral_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N)
    (s : Spins M) (i j : Fin M) :
    (∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i-x j‖) =
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x (e j)‖ := by
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, reindexForm] using
    integral_reindex e (fun x => ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x (e j)‖)

lemma pair_sum_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) (s : Spins M) :
    (∑ i : Fin M, ∑ j : Fin M, if i < j then
      ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i-x j‖ else 0) =
    ∑ i : Fin N, ∑ j : Fin N, if i < j then
      ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i-x j‖ else 0 := by
  classical
  rw [sum_pairs_half _ (fun i j => integral_congr_ae
    (Filter.Eventually.of_forall fun x => by rw [norm_sub_rev (x i) (x j)]))]
  rw [sum_pairs_half _ (fun i j => integral_congr_ae
    (Filter.Eventually.of_forall fun x => by rw [norm_sub_rev (x i) (x j)]))]
  simp_rw [pair_integral_reindex e]
  congr 1
  rw [← Equiv.sum_comp e (fun i => ∑ j : Fin N, if i ≠ j then
    ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i-x j‖ else 0)]
  apply Finset.sum_congr rfl; intro i _
  rw [← Equiv.sum_comp e (fun j => if e i ≠ j then
    ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x (e i)-x j‖ else 0)]
  simp only [ne_eq, e.injective.eq_iff]

theorem formEnergy_reindex {M N : ℕ} (e : Fin M ≃ Fin N) (ψ : FormVector N) (Z : ℝ) :
    formEnergy Z (reindexForm e ψ) = formEnergy Z ψ := by
  unfold formEnergy
  have hk (s : Spins M) : (∑ i : Fin M, ∑ a : Fin 3,
      ∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
      ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient (s ∘ e.symm) i a x‖ ^ 2 := by
    have h (i : Fin M) (a : Fin 3) :
        (∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
        ∫ x, ‖ψ.gradient (s ∘ e.symm) (e i) a x‖ ^ 2 :=
      integral_reindex e (fun x => ‖ψ.gradient (s ∘ e.symm) (e i) a x‖ ^ 2)
    simp_rw [h]
    exact Equiv.sum_comp e (fun i => ∑ a : Fin 3, ∫ x, ‖ψ.gradient (s ∘ e.symm) i a x‖ ^ 2)
  have hn (s : Spins M) : (∑ i : Fin M,
      ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
      ∑ i : Fin N, ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i‖ := by
    simp_rw [nuclear_integral_reindex e]
    exact Equiv.sum_comp e (fun i => ∫ x, ‖ψ.value (s ∘ e.symm) x‖ ^ 2 / ‖x i‖)
  rw [show (∑ s, ∑ i, ∑ a, ∫ x, ‖(reindexForm e ψ).gradient s i a x‖ ^ 2) =
    ∑ s : Spins N, ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2 by
      simp_rw [hk]; exact sum_spin_reindex e (fun s => ∑ i, ∑ a, ∫ x, ‖ψ.gradient s i a x‖ ^ 2)]
  rw [show (∑ s, ∑ i, ∫ x, ‖(reindexForm e ψ).value s x‖ ^ 2 / ‖x i‖) =
    ∑ s : Spins N, ∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ by
      simp_rw [hn]; exact sum_spin_reindex e (fun s => ∑ i, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖)]
  congr 1
  simp_rw [pair_sum_reindex e]
  exact sum_spin_reindex e (fun s => ∑ i, ∑ j, if i < j then
    ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i-x j‖ else 0)


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators

end CoulombAtom

end

end OAI
