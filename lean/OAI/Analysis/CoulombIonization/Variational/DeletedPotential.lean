import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CutOuterLaw
import OAI.Analysis.CoulombIonization.Variational.PotentialRecovery

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

def outerDeletedPotential {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) : ℝ :=
  ∑ i, if t-7*b ≤ ‖u i-y‖ then 1/‖u i-y‖ else 0

lemma outerDeletedPotential_nonneg {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    0 ≤ outerDeletedPotential y t b u := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> positivity

lemma outerDeletedPotential_measurable {M : ℕ} (y : Space) (t b : ℝ) :
    Measurable (outerDeletedPotential (M := M) y t b) := by
  apply Finset.measurable_sum; intro i _
  exact (measurable_const.div (configuration_distance_measurable y i)).ite
    (measurableSet_le measurable_const (configuration_distance_measurable y i)) measurable_const

lemma outerDeletedPotential_le_count {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t)
    (u : Configuration M) :
    outerDeletedPotential y t b u ≤ outerDeletedCount y t b u/(t-7*b) := by
  rw [outerDeletedCount,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact one_div_le_one_div_of_le (by linarith) hi
  · simp

lemma outerDeletedPotential_le {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t) (u : Configuration M) :
    outerDeletedPotential y t b u ≤ M/(t-7*b) :=
  (outerDeletedPotential_le_count y h u).trans
    (div_le_div_of_nonneg_right (outerDeletedCount_le y t b u) (by linarith))

lemma weighted_outerDeletedPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {t b : ℝ} (h : 7*b < t) :
    Integrable (fun u => outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) :=
  (hψ.coreSlice_mass_integrable s).bdd_mul
    (outerDeletedPotential_measurable y t b).aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (outerDeletedPotential_nonneg y t b u)]
      exact outerDeletedPotential_le y h u))

theorem fresh_cut_deleted_potential_bound {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (h : 7*b < t) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      outerDeletedPotential y t b u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u))/(t-7*b) := by
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) => outerDeletedCount y t b u
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ c
  have hi (i : I) : Integrable (fun u => f i u*w i u) :=
    ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      (outerDeletedCount_measurable y t b).aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_of_nonneg (outerDeletedCount_nonneg y t b u)]
        exact outerDeletedCount_le y t b u))
  have hi2 (i : I) : Integrable (fun u => w i u*(f i u)^2) := by
    have H := ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      ((outerDeletedCount_measurable y t b).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg y t b u)
        (outerDeletedCount_le y t b u)))
    simpa only [mul_comm] using H
  have hcs := finite_weighted_abs_bound
    (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun _ => (outerDeletedCount_measurable y t b).aestronglyMeasurable) hi2
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ
  have hc (i : I) : (∫ u, outerDeletedPotential y t b u*w i u) ≤
      (∫ u, f i u*w i u)/(t-7*b) := by
    rw [←integral_div]
    apply integral_mono (weighted_outerDeletedPotential_integrable (hχ i.1) i.2 y h)
      ((hi i).div_const _)
    intro u
    have hh := mul_le_mul_of_nonneg_right (outerDeletedPotential_le_count y h u)
      (formMass_nonneg (coreSlice (orderedCutForm p hp ψ i.1) i.2 u))
    simpa only [div_mul_eq_mul_div] using hh
  rw [hmass] at hcs
  have hcauchy : (∑ i : I, ∫ u, f i u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u) := by
    simpa only [f,abs_of_nonneg (outerDeletedCount_nonneg y t b _),mul_comm] using hcs
  have hd : (∑ i : I, ∫ u, outerDeletedPotential y t b u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u)/(t-7*b) := calc
    _ ≤ (∑ i : I, ∫ u, f i u*w i u)/(t-7*b) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _ => hc i)
    _ ≤ _ := div_le_div_of_nonneg_right hcauchy (by linarith)
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at hd
  simpa only [w,f] using hd

end CoulombAtom

end

end OAI
