import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CutOuterLaw
import OAI.Analysis.CoulombIonization.FieldAnalysis.OuterFieldMaximum
import OAI.Analysis.CoulombIonization.Variational.WeightedCauchy

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Filter
open scoped BigOperators

namespace CoulombAtom

lemma sum_deleted_field_le_max {M : ℕ} (u : Configuration M) (y : Space) (t b : ℝ)
    (f : Fin M → ℝ) {F : ℝ} (hF : ∀ i, f i ≤ F) :
    (∑ i, f i)-(∑ i ∈ Finset.univ.filter (fun i => ‖u i-y‖ < t-7*b), f i) ≤
      F*outerDeletedCount y t b u := by
  classical
  simp only [Finset.sum_filter,←Finset.sum_sub_distrib,outerDeletedCount,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : ‖u i-y‖ < t-7*b
  · simp only [hi,ite_eq_left,not_le.mpr hi,ite_false,mul_zero,sub_self,le_refl]
  · simp only [hi,ite_false,not_lt.mp hi,ite_eq_left,mul_one,sub_zero]
    exact hF i

lemma radial_deleted_field_le_max {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (s : Spins (cutOutNumber c)) (y : Space) (t b Z lam : ℝ)
    (u : Configuration (cutOutNumber c)) :
    conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u ≤
      conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u*
        outerDeletedCount y t b u*formMass (coreSlice (orderedCutForm p hp ψ c) s u) := by
  unfold conditionalFieldSum conditionalRetainedFieldSum radialPatchRetention
  rw [←mul_sub,mul_comm (formMass _)]
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact sum_deleted_field_le_max u y t b _ (conditionalField_le_outMaximum Z lam _ s u)

def freshOutMaximumSecondMoment {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
    conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u^2*
      formMass (coreSlice (orderedCutForm p hp ψ c) s u)

lemma freshOutMaximumSecondMoment_nonneg {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L) (Z lam : ℝ) :
    0 ≤ freshOutMaximumSecondMoment p hp ψ Z lam := by
  apply Finset.sum_nonneg; intro c _
  apply Finset.sum_nonneg; intro s _
  exact integral_nonneg (fun u => mul_nonneg (sq_nonneg _) (formMass_nonneg _))

lemma radial_deleted_max_product_integrable {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let χ := orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalOutMaximum Z lam χ s u*outerDeletedCount y t b u*
      formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) hψ c
  apply (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalOutMaximum_aemeasurable hχ s Z lam).mul (outerDeletedCount_measurable y t b).aemeasurable).aestronglyMeasurable
  apply ae_of_all; intro u
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _) (outerDeletedCount_nonneg _ _ _ _))]
  exact mul_le_mul (radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u)
    (outerDeletedCount_le y t b u) (outerDeletedCount_nonneg y t b u) (by positivity)

lemma weighted_outerDeleted_sq_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) (t b : ℝ) :
    Integrable (fun u => outerDeletedCount y t b u^2*formMass (coreSlice ψ s u)) := by
  exact (hψ.coreSlice_mass_integrable s).bdd_mul
    ((outerDeletedCount_measurable y t b).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg _ _ _ _) (outerDeletedCount_le _ _ _ _)))

theorem radial_deleted_field_budget {L : ℕ} {ψ : FormVector L} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u-
      conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) s (radialPatchRetention L y t b c s) u) ≤
      Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
        Real.sqrt (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  dsimp only
  have hh := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ cs.1) cs.2 u)
    (fun _ u => outerDeletedCount y t b u)
    (fun _ _ => formMass_nonneg _)
    (fun cs => radial_outMaximum_square_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
    (fun cs => weighted_outerDeleted_sq_integrable (orderedCutForm_sobolev p hp hψ cs.1) cs.2 y t b)
    (fun cs => radial_deleted_max_product_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
  simp only [Fintype.sum_sigma] at hh
  apply le_trans _ hh
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  have hχ := orderedCutForm_sobolev p hp hψ c
  apply integral_mono
    ((conditionalFieldSum_integrable hχ Z lam s).sub
      (conditionalRetainedFieldSum_integrable hχ Z lam s _ (radialPatchRetention_measurable L y t b c s)))
    (radial_deleted_max_product_integrable hψ y ht hb hy hZ hlam c s)
  exact radial_deleted_field_le_max p hp ψ c s y t b Z lam

end CoulombAtom

end

end OAI
