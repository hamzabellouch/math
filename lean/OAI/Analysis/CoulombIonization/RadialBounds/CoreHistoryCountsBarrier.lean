import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialCountSelection
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryMassBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators

lemma rawBallCount_cutCore_le {N : ℕ} (c : Fin N → Fin 2) (x : Configuration N)
    (y : Space) (R : ℝ) : rawBallCount y R (cutCorePositions c x) ≤ rawBallCount y R x := by
  rw [rawBallCount,sum_cutCorePositions c x (fun z => if ‖z-y‖ < R then 1 else 0)]
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> norm_num

def rawCountMoment {N : ℕ} (ψ : FormVector N) (y : Space) (R : ℝ) : ℝ :=
  rawFormPair ψ (fun x => rawBallCount y R x^2)

lemma rawCountMoment_nonneg {N : ℕ} (ψ : FormVector N) (y : Space) (R : ℝ) :
    0 ≤ rawCountMoment ψ y R :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

lemma rawCountMoment_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) : rawCountMoment ψ y R = ∫ x, rawBallCount y R x^2 ∂formRawLaw ψ :=
  rawFormPair_eq_integral hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))

lemma rawCountMoment_coreSlice_integrable {N M : ℕ} {ψ : FormVector (N+M)} (hψ : SobolevVector ψ)
    (y : Space) (R : ℝ) (t : Spins M) :
    Integrable (fun v => rawCountMoment (coreSlice ψ t v) y R) :=
  rawFormPair_coreSlice_integrable hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x)) t

lemma sum_cutCore_countMoment_le {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp ψ c)
      (fun φ => rawCountMoment φ y R)) ≤ rawCountMoment ψ y R := by
  simp only [rawCountMoment]
  simp_rw [cutCore_rawFormPair p hp hψ _ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))]
  rw [rawFormPair_eq_integral hψ ((rawBallCount_measurable y R).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg y R x) (rawBallCount_le y R x))]
  change spatialCutExpectation p hp ψ (fun c x => rawBallCount y R (cutCorePositions c x)^2) ≤ _
  apply spatialCutExpectation_le_raw p hp hψ
    (fun c => ((rawBallCount_measurable y R).comp (cutCorePositions_measurable c)).pow_const 2)
    (A := (N:ℝ)^2)
    (fun c x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _)
      ((rawBallCount_cutCore_le c x y R).trans (rawBallCount_le _ _ _)))
    ((rawBallCount_measurable y R).pow_const 2) (B := (N:ℝ)^2)
    (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _))
  intro c x _
  exact pow_le_pow_left₀ (rawBallCount_nonneg _ _ _) (rawBallCount_cutCore_le c x y R) 2

lemma nextCoreObservation_count_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (y : Space) (R : ℝ) (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c)
      (fun φ => rawCountMoment φ y R)) :=
  nextCoreObservation_statistic_integrable ψ p hp c (fun φ => rawCountMoment φ y R)
    (fun s => rawCountMoment_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) y R s) t

lemma sum_nextCoreObservation_count_eq {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp ψ c)
      (fun φ => rawCountMoment φ y R)) =
    ∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
      coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (fun φ => rawCountMoment φ y R) := by
  have ht (c : Fin N → Fin 2) := coreLawAverage_next ψ p hp c
    (fun φ => rawCountMoment φ y R)
    (fun s => rawCountMoment_coreSlice_integrable (nextCoreObservation_sobolev hψ p hp c) y R s)
  simp_rw [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact (integral_finsetSum _ (fun c _ =>
    nextCoreObservation_count_statistic_integrable hψ p hp c y R t)).symm

theorem sum_nextCoreObservation_countMoment_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp ψ c)
      (fun φ => rawCountMoment φ y R)) ≤
      coreLawAverage ψ (fun φ => rawCountMoment φ y R) := by
  rw [sum_nextCoreObservation_count_eq hψ p hp y R]
  change (∑ t : Spins M, ∫ v, ∑ c : Fin N → Fin 2,
      coreLawAverage (orderedCutForm p hp (coreSlice ψ t v) c) (fun φ => rawCountMoment φ y R)) ≤
    ∑ t : Spins M, ∫ v, rawCountMoment (coreSlice ψ t v) y R
  apply Finset.sum_le_sum
  intro t _
  apply integral_mono_ae
    (integrable_finsetSum _ (fun c _ => nextCoreObservation_count_statistic_integrable hψ p hp c y R t))
    (rawCountMoment_coreSlice_integrable hψ y R t)
  filter_upwards [hψ.ae_coreSlice t] with v hv
  exact sum_cutCore_countMoment_le hv p hp y R

namespace CoreObservationGraph

def countMoment (G : CoreObservationGraph) (y : Space) (R : ℝ) : ℝ :=
  coreLawAverage G.vector (fun φ => rawCountMoment φ y R)

lemma countMoment_nonneg (G : CoreObservationGraph) (y : Space) (R : ℝ) : 0 ≤ G.countMoment y R :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => rawCountMoment_nonneg _ _ _))

lemma observe_countMoment (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).countMoment y R) ≤ G.countMoment y R :=
  sum_nextCoreObservation_countMoment_le G.sobolev p hp y R

end CoreObservationGraph

open MeasureTheory Filter
open scoped BigOperators

lemma rawBallCount_le_of_radius {N : ℕ} (x : Configuration N) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : rawBallCount y R x ≤ rawBallCount z S x := by
  unfold rawBallCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hy hz hz
  · norm_num
  · exfalso
    apply hz
    have hh : ‖x i-z‖ ≤ ‖x i-y‖+‖y-z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (x i-y) (y-z)
    linarith
  · norm_num
  · norm_num

lemma rawCountMoment_le_of_radius {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y z : Space) {R S : ℝ} (h : ‖y-z‖+R ≤ S) : rawCountMoment ψ y R ≤ rawCountMoment ψ z S := by
  have hi (w : Space) (r : ℝ) (s : Spins N) : Integrable (fun x => rawBallCount w r x^2*‖ψ.value s x‖^2) :=
    ((hψ.1 s).norm.integrable_sq).bdd_mul ((rawBallCount_measurable w r).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawBallCount_nonneg _ _ _) (rawBallCount_le _ _ _)))
  unfold rawCountMoment rawFormPair
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono (hi y R s) (hi z S s)
  intro x
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (rawBallCount_nonneg _ _ _)
    (rawBallCount_le_of_radius x y z h) 2) (sq_nonneg _)

namespace CoreObservationGraph

lemma countMoment_le_of_radius (G : CoreObservationGraph) (y z : Space) {R S : ℝ}
    (h : ‖y-z‖+R ≤ S) : G.countMoment y R ≤ G.countMoment z S := by
  unfold countMoment coreLawAverage
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae (rawCountMoment_coreSlice_integrable G.sobolev y R s)
    (rawCountMoment_coreSlice_integrable G.sobolev z S s)
  filter_upwards [G.sobolev.ae_coreSlice s] with u hu
  exact rawCountMoment_le_of_radius hu y z h

end CoreObservationGraph

end CoulombAtom

end

end OAI
