import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicBudgetScreening
import OAI.Analysis.CoulombRadii.ThomasFermi.BinaryEnsemble
import OAI.Analysis.CoulombRadii.Localization.ThinIMS

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma expectedPopulation_nonneg {n : ℕ} (ψ : H1Vector n) (A : Set Space) :
    0≤expectedPopulation ψ A := by
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.sum_nonneg
  intro i hi
  exact integral_nonneg (fun x => mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (sq_nonneg _))

lemma expectedPopulation_mono {n : ℕ} (ψ : H1Vector n) {A B : Set Space}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A⊆B) :
    expectedPopulation ψ A≤expectedPopulation ψ B := by
  rw [expectedPopulation_eq ψ hA,expectedPopulation_eq ψ hB]
  apply Finset.sum_le_sum
  intro s hs
  apply integral_mono_of_nonneg
  · exact Eventually.of_forall (fun x => mul_nonneg (localCount_nonneg _ _) (sq_nonneg _))
  · simpa only [pow_one] using localCount_weight_integrable ψ hB s 1
  · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_right (localCount_mono hAB x) (sq_nonneg _))

def thinIMS {n : ℕ} (ψ : H1Vector n) (y : Space) (t b : ℝ) : ℝ :=
  3*(thinCutCoefficient/b)^2*expectedPopulation ψ (Metric.closedBall y (t+b))

lemma thinIMS_nonneg {n : ℕ} (ψ : H1Vector n) (y : Space) (t b : ℝ) : 0≤thinIMS ψ y t b := by
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (expectedPopulation_nonneg _ _)

theorem thin_localization {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    (y : Space) {t b : ℝ} (ht : 0≤t) (hb : 0<b) :
    ∃ T : RecordedEnsemble n, T.Conserves ψ ∧ T.CoreFermionic ∧ T.OutFermionic ∧
      T.CoreSupported {z | t≤‖z-y‖} ∧ T.OutSupported (Metric.closedBall y (t+b)) ∧
      T.totalMass=mass ψ ∧ T.totalForm S≤form S ψ+thinIMS ψ y t b := by
  obtain ⟨T,hC,hc,ho,hcs,hos,hm,hf⟩ := RecordedEnsemble.binary_localization S ψ hψ
    (thinCut y t b) (thinCut_smooth y t b) (thinCut_partition y t b)
    (thinCutCoefficient/b) (div_nonneg thinCutCoefficient_pos.le hb.le)
    (thinCut_derivative_bound y ht hb) (Metric.closedBall y (t+b)) {z | t≤‖z-y‖}
    (fun z hz => thinCut_out_zero y ht hb z (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using (show t+b≤‖z-y‖ from le_of_lt (by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hz))))
    (fun z hz => thinCut_core_zero y ht hb z (le_of_lt (by simpa only [Set.mem_ofPred_eq,not_le] using hz)))
  refine ⟨T,hC,hc,ho,hcs,hos,hm,?_⟩
  rw [hf]
  exact form_thin_labelCut S ψ y ht hb

theorem thin_localization_history {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    {y : Space} (hy : y≠0) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (hwidth : t+b≤80*atomicCellScale y) :
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      (∀ i, T.target i=y) ∧ T.ensemble.OutFermionic ∧
      T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) := by
  obtain ⟨U,hC,hc,ho,hcs,hos,hm,hf⟩ := thin_localization S ψ hψ y ht hb
  let T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1 := {
    ensemble := U
    target := fun _ => y
    nonzero := fun _ => hy
    law := hC
    fermionic := hc
    support := by
      intro p
      apply (hos p).mono_space
      intro z hz
      apply Set.mem_iUnion.mpr
      refine ⟨0,?_⟩
      exact Metric.closedBall_subset_closedBall hwidth hz
    mass_eq := hm
    energy := by
      apply hf.trans
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (expectedPopulation_nonneg _ _)) }
  exact ⟨T,fun _ => rfl,ho,hcs,hos⟩

theorem thin_localization_raw_control {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (hwidth : t+b≤80*atomicCellScale y)
    (hbudget : thinIMS ψ y t b≤ screenCountParameter ψ δ*screenEnergy δ (atomicCellScale y)) :
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      (∀ v, AtomicScaleWindow (atomicCellScale y) 4 v →
        Real.sqrt (T.ensemble.rawSquare S v (atomicCellScale v))≤
          2*atomicBudgetRecursionC^3*screenFieldUnit δ (screenCountParameter ψ δ) (atomicCellScale y)) := by
  obtain ⟨T,htarget,ho,hcs,hos⟩ := thin_localization_history S ψ hψ hy ht hb hwidth
  refine ⟨T,ho,hcs,hos,?_⟩
  intro v hv
  apply T.positive_field_actual_counts S hatom ψ hm hE hstate hbudget hδ (atomicCellScale_pos hy)
  · intro i
    rw [htarget i]
    constructor <;> norm_num <;> linarith [atomicCellScale_nonneg y]
  · simpa only [pow_one] using hv

end Coulomb
end

end
end

end OAI
