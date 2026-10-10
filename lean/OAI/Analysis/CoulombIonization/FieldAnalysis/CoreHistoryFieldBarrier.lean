import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.OuterFieldMaximum
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryMassBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.QuantumFieldExcessBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

def coreFieldSquare {N : ℕ} (Z lam : ℝ) (y : Space) (ψ : FormVector N) : ℝ :=
  (max (normalizedCoreField Z lam ψ y) 0)^2*formMass ψ

lemma coreFieldSquare_nonneg {N : ℕ} (Z lam : ℝ) (y : Space) (ψ : FormVector N) :
    0 ≤ coreFieldSquare Z lam y ψ := mul_nonneg (sq_nonneg _) (formMass_nonneg _)

lemma coreFieldSquare_le_nuclear {N : ℕ} (ψ : FormVector N) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    coreFieldSquare Z lam y ψ ≤ (Z/‖y‖)^2*formMass ψ := by
  apply mul_le_mul_of_nonneg_right _ (formMass_nonneg _)
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le (normalizedCoreField_le_nuclear ψ hZ hlam y) (div_nonneg hZ (norm_nonneg _))) 2

lemma coreFieldSquare_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    Integrable (fun u => coreFieldSquare Z lam y (coreSlice ψ s u)) := by
  apply (hψ.coreSlice_mass_integrable s).bdd_mul
    (((normalizedCoreField_eval_aemeasurable hψ s Z lam y).max aemeasurable_const).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_le (normalizedCoreField_le_nuclear _ hZ hlam y) (div_nonneg hZ (norm_nonneg _))) 2

lemma sum_nextCoreObservation_fieldSquare {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    (∑ c : Fin N → Fin 2,
      coreLawAverage (nextCoreObservation p hp ψ c) (coreFieldSquare Z lam y)) =
      ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
        coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (coreFieldSquare Z lam y) := by
  have hi (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) :=
    coreFieldSquare_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) s hZ hlam y
  have ht (c : Fin N → Fin 2) := coreLawAverage_next ψ p hp c
    (coreFieldSquare Z lam y) (hi c)
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_statistic_integrable ψ p hp c _ (hi c) t)).symm

namespace CoreObservationGraph

def fieldMoment (G : CoreObservationGraph) (Z lam : ℝ) (y : Space) : ℝ :=
  coreLawAverage G.vector (coreFieldSquare Z lam y)

def excess (G : CoreObservationGraph) (Z lam : ℝ) : ℝ :=
  coreLawAverage G.vector (corePriceExcess Z lam)

lemma fieldMoment_nonneg (G : CoreObservationGraph) (Z lam : ℝ) (y : Space) :
    0 ≤ G.fieldMoment Z lam y :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => coreFieldSquare_nonneg _ _ _ _))

lemma fieldMoment_le_nuclear (G : CoreObservationGraph) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) :
    G.fieldMoment Z lam y ≤ (Z/‖y‖)^2*G.mass := by
  rw [fieldMoment,mass,←coreLawAverage_mass G.sobolev]
  unfold coreLawAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  rw [←integral_const_mul]
  exact integral_mono (coreFieldSquare_coreSlice_integrable G.sobolev t hZ hlam y)
    ((G.sobolev.coreSlice_mass_integrable t).const_mul _)
    (fun _ => coreFieldSquare_le_nuclear _ hZ hlam y)

theorem fieldMoment_le_observe_excess (G : CoreObservationGraph)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    G.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*G.mass+
      (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).excess Z lam)/B) := by
  have hi (t : Spins G.outSize) := integrable_finsetSum Finset.univ (fun c _ =>
    nextCoreObservation_excess_statistic_integrable G.sobolev p hp c t Z lam)
  have hbound (t : Spins G.outSize) :
      (∫ v, coreFieldSquare Z lam y (coreSlice G.vector t v)) ≤
        ∫ v, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice G.vector t v)+
          (∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B) := by
    apply integral_mono_ae (coreFieldSquare_coreSlice_integrable G.sobolev t hZ hlam.le y)
      (((G.sobolev.coreSlice_mass_integrable t).const_mul _ |>.add ((hi t).div_const B)).const_mul _)
    filter_upwards [G.antisymmetric.ae_coreSlice G.sobolev t] with v hvs
    exact parent_field_sq_mass_le_fresh_core_excess p hp hvs y hB hnuc hv hd hZ hlam
  have he (t : Spins G.outSize) :
      (∫ v, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice G.vector t v)+
        (∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B)) =
      2*packetFieldConstant^2*((1/B^4+1/B)^2*(∫ v, formMass (coreSlice G.vector t v))+
        (∫ v, ∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector t v) c)/B) := by
    rw [integral_const_mul,integral_add ((G.sobolev.coreSlice_mass_integrable t).const_mul _)
      ((hi t).div_const B),integral_const_mul,integral_div]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hbound t)
  simp_rw [he] at hh
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] at hh
  rw [G.sobolev.integral_coreSlice_mass] at hh
  change G.fieldMoment Z lam y ≤ _ at hh
  change G.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass G.vector+
    (∑ c : Fin G.coreSize → Fin 2,
      coreLawAverage (nextCoreObservation p hp G.vector c) (corePriceExcess Z lam))/B)
  rw [sum_nextCoreObservation_excess G.sobolev p hp Z lam]
  exact hh

end CoreObservationGraph
end CoulombAtom

end

end OAI
