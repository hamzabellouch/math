import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CutOuterLaw
import OAI.Analysis.CoulombIonization.FormDomain.ShiftedCoulombIntegrable

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_IntegrableCutTower_scope

open MeasureTheory Set Filter
open scoped BigOperators

lemma weighted_coreSlice_eq_full_integrable {N M : ℕ}
    (ψ : FormVector (N+M)) (g : Configuration M → ℝ)
    (hi : ∀ s : Spins (N+M), Integrable (fun x => g (outProjection x)*‖ψ.value s x‖^2)) :
    (∑ s : Spins M, ∫ u, g u*formMass (coreSlice ψ s u)) =
      ∑ s : Spins (N+M), ∫ x, g (outProjection x)*‖ψ.value s x‖^2 := by
  have hj (s : Spins N) (t : Spins M) : Integrable (fun p : Configuration N × Configuration M =>
      g p.2*‖ψ.value (joinLists s t) (joinLists p.1 p.2)‖^2) := by
    simpa only [outProjection_join] using integrable_join (N := N) (M := M) (hi (joinLists s t))
  have hk (s : Spins N) (t : Spins M) : Integrable (fun u : Configuration M =>
      g u*(∫ v : Configuration N, ‖ψ.value (joinLists s t) (joinLists v u)‖^2)) := by
    simpa only [integral_const_mul] using (hj s t).integral_prod_right
  simp only [formMass,Finset.mul_sum,coreSlice]
  simp_rw [integral_finsetSum _ (fun s _ => hk s _),←integral_const_mul]
  have he (s : Spins N) (t : Spins M) :
      (∫ u : Configuration M, ∫ v : Configuration N,
        g u*‖ψ.value (joinLists s t) (joinLists v u)‖^2) =
      ∫ x, g (outProjection x)*‖ψ.value (joinLists s t) x‖^2 := by
    simpa only [outProjection_join] using integral_join (N := N) (M := M) (hi (joinLists s t))
  simp_rw [he]
  exact sum_spin_join (fun s : Spins (N+M) =>
    ∫ x, g (outProjection x)*‖ψ.value s x‖^2)

lemma cutOuter_expectation_eq_full_integrable {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (g : Configuration (cutOutNumber c) → ℝ)
    (hi : ∀ s : Spins (cutCoreNumber c+cutOutNumber c), Integrable (fun x =>
      g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2)) :
    (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∑ s : Spins L, ∫ x, g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
  rw [weighted_coreSlice_eq_full_integrable _ _ hi]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutOutPositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

end Work_IntegrableCutTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

def rawLocalPotential {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) : ℝ :=
  ∑ i, if ‖x i-y‖ < q then 1/‖x i-y‖ else 0

lemma rawLocalPotential_nonneg {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    0 ≤ rawLocalPotential y q x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · positivity
  · exact le_rfl

lemma rawLocalPotential_measurable (N : ℕ) (y : Space) (q : ℝ) :
    Measurable (rawLocalPotential (N := N) y q) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (configuration_distance_measurable y i) measurable_const)
    (measurable_const.div (configuration_distance_measurable y i)) measurable_const

lemma rawLocalPotential_weighted_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q x*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_core_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) (q : ℝ) :
    Integrable (fun u => rawLocalPotential y q u*formMass (coreSlice ψ s u)) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (coreSlice_mass_shifted_integrable hψ s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_out_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins (N+M)) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (outProjection x)*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul,outProjection]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y).indicator
    (measurableSet_lt (configuration_distance_measurable y (finSumFinEquiv (Sum.inr i))) (measurable_const (a := q)))
  convert hi using 1
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_cutOutPositions_le {N : ℕ} (y : Space) (q : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) :
    rawLocalPotential y q (cutOutPositions c x) ≤ rawLocalPotential y q x := by
  classical
  let e : Fin (cutOutNumber c) → Fin N := fun i => cutOrder c (finSumFinEquiv (Sum.inr i))
  have hinj : Function.Injective e :=
    (cutOrder c).injective.comp (finSumFinEquiv.injective.comp Sum.inr_injective)
  let k : Fin N → ℝ := fun i => if ‖x i-y‖ < q then 1/‖x i-y‖ else 0
  have hn (i : Fin N) : 0 ≤ k i := by dsimp only [k]; split_ifs <;> positivity
  change (∑ i, k (e i)) ≤ ∑ i, k i
  calc
    _ = ∑ i ∈ Finset.univ.image e, k i := (Finset.sum_image (fun i _ j _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hn i)

lemma rawLocalPotential_cut_weighted_integrable {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (c : Fin N → Fin 2)
    (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (cutOutPositions c x)*
      ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) := by
  have hmp := (hψ.multiply (spatialProduct p hp c)).1 s
  have hmeas : Measurable (cutOutPositions c) := by
    apply Measurable.of_eval
    exact fun _ => measurable_pi_apply _
  apply (rawLocalPotential_weighted_integrable (hψ.multiply (spatialProduct p hp c)) s y q).mono'
    (((rawLocalPotential_measurable _ y q).comp hmeas).aestronglyMeasurable.mul
      (hmp.aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (rawLocalPotential_nonneg _ _ _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _)

theorem fresh_cut_raw_local_control {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) (q : ℝ) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      rawLocalPotential y q u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      ∫ x, rawLocalPotential y q x ∂formRawLaw ψ := by
  have htw (c : Fin N → Fin 2) := cutOuter_expectation_eq_full_integrable p hp ψ c
    (rawLocalPotential y q)
    (fun s => rawLocalPotential_out_weighted_integrable (orderedCutForm_sobolev p hp hψ c) s y q)
  simp_rw [htw]
  have hb : (∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
      rawLocalPotential y q (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) ≤
      ∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
        rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
    apply Finset.sum_le_sum; intro c _
    apply Finset.sum_le_sum; intro s _
    exact integral_mono (rawLocalPotential_cut_weighted_integrable p hp hψ c s y q)
      (rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)
      (fun x => mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _))
  apply hb.trans_eq
  rw [Finset.sum_comm,formRawLaw_integral hψ]
  have he (s : Spins N) : (∑ c : Fin N → Fin 2, ∫ x,
      rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) =
      ∫ x, rawLocalPotential y q x*‖ψ.value s x‖^2 := by
    rw [←integral_finsetSum _ (fun c _ => rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [←Finset.mul_sum,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]
  simp_rw [he]
  rw [←integral_finsetSum _ (fun s _ => rawLocalPotential_weighted_integrable hψ s y q)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [←Finset.mul_sum,formRawDensity,mul_comm]

end CoulombAtom

end

end OAI
