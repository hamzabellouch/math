import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.CoupledCoreExcessBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.ThinFieldFeedbackBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PatchMassSubmean_barrier_scope

open MeasureTheory Set Metric Filter
open scoped ENNReal

open CoulombAnalysis CoulombNeumann

lemma conditionalPatchField_le_submean {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R Z lam : ℝ} (ha : 0 < a) (hsep : R+2*a ≤ ‖y‖)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    ∀ᵐ z ∂ballMeasure R, conditionalPatchField ψ s Z lam y R u z ≤
      Real.sqrt ((1/(a^3*(Real.pi*4/3)))*∫ x in closedBall y (R+a),
        (max (normalizedCoreField Z lam (coreSlice ψ s u) x) 0)^2) := by
  let Q := (1/(a^3*(Real.pi*4/3)))*∫ x in closedBall y (R+a),
        (max (normalizedCoreField Z lam (coreSlice ψ s u) x) 0)^2
  have hQ : 0 ≤ Q := by dsimp [Q]; exact mul_nonneg (by positivity) (integral_nonneg (fun _ => sq_nonneg _))
  by_cases hp : MemLp (fun z => normalizedCoreField Z lam (coreSlice ψ s u) (y+z)) (5/2) (ballMeasure R)
  · filter_upwards [conditionalPatchField_ae ψ s Z lam y R u hp,
      ae_restrict_mem measurableSet_ball] with z hz hmem
    rw [hz]
    have hnorm : ‖(y+z)-y‖ ≤ R := by simp only [add_sub_cancel_left]; exact (mem_ball_zero_iff.mp hmem).le
    have hh := core_field_sq_le_ball_average hψ y (y+z) ha hsep hnorm hZ hlam
    apply (le_max_left _ _).trans
    exact (Real.le_sqrt (le_max_right _ _) hQ).2 hh
  · have hz : conditionalPatchField ψ s Z lam y R u = 0 := by
      simp only [conditionalPatchField,toLpOrZero,dite_eq_right hp]
    rw [hz]
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := (5/2:ℝ≥0∞)) (μ := ballMeasure R)] with z hz
    rw [hz]
    exact Real.sqrt_nonneg _

lemma weightedPatchMass_le_submean {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (hψ : SobolevVector (coreSlice ψ s u))
    (y : Space) {a R Z lam : ℝ} (ha : 0 < a) (hR : 0 < R) (hsep : R+2*a ≤ ‖y‖)
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    weightedPatchMass ψ s Z lam y R u ≤
      (4*R*Real.sqrt (1/(a^3*(Real.pi*4/3))))*
      (Real.sqrt (∫ z in closedBall y (R+a), coreFieldSquare Z lam z (coreSlice ψ s u))*
        Real.sqrt (formMass (coreSlice ψ s u))) := by
  let φ := coreSlice ψ s u
  let B := 1/(a^3*(Real.pi*4/3))
  let I := ∫ z in closedBall y (R+a), (max (normalizedCoreField Z lam φ z) 0)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : 0 ≤ I := integral_nonneg (fun _ => sq_nonneg _)
  have hM := formMass_nonneg φ
  have hm := tfPatchMinimizer_mass_le hR tfKinetic_pos (Real.sqrt_nonneg _)
    (conditionalPatchField ψ s Z lam y R u)
    (conditionalPatchField_le_submean ψ s u hψ y ha hsep hZ hlam)
  have hh := mul_le_mul_of_nonneg_left hm hM
  change weightedPatchMass ψ s Z lam y R u ≤ formMass φ*(4*R*Real.sqrt (B*I)) at hh
  apply hh.trans_eq
  simp only [coreFieldSquare,integral_mul_const]
  change formMass φ*(4*R*Real.sqrt (B*I)) =
    (4*R*Real.sqrt B)*(Real.sqrt (I*formMass φ)*Real.sqrt (formMass φ))
  rw [Real.sqrt_mul hB,Real.sqrt_mul hI]
  have he : Real.sqrt (formMass φ)*Real.sqrt (formMass φ) = formMass φ := by
    nlinarith [Real.sq_sqrt hM]
  calc _ = (4*R*Real.sqrt B)*(Real.sqrt I*(Real.sqrt (formMass φ)*Real.sqrt (formMass φ))) := by rw [he]; ring
    _ = _ := by ring

end Work_PatchMassSubmean_barrier_scope

open MeasureTheory
open scoped BigOperators

namespace CoreObservationEnsemble

lemma initial_observe_fieldMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (z : Space) :
    ((initial ψ hψ).observe p hp).fieldMoment Z lam z =
      ∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp ψ c) (coreFieldSquare Z lam z) := by
  change (∑ ic : Σ _ : Unit, Fin N → Fin 2,
    coreLawAverage (nextCoreObservation (M := 0) p hp ψ ic.2) (coreFieldSquare Z lam z)) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.univ_unique,Finset.sum_singleton]
  have hh := sum_nextCoreObservation_fieldSquare (M := 0) hψ.sobolevVector p hp hZ hlam z
  change _ = coreLawAverage (M := 0) ψ (fun φ =>
    ∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp φ c) (coreFieldSquare Z lam z)) at hh
  rwa [coreLawAverage_empty] at hh

lemma initial_outMoment {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ)
    (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (initial ψ hψ).outMoment y hr hb Z lam =
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb)
        (coreFirstRadialCut_partition y hr hb) ψ Z lam := by
  change (∑ _i : Unit, (CoreObservationGraph.initial ψ hψ).outMoment y hr hb Z lam) = _
  simp only [Finset.univ_unique,Finset.sum_singleton]
  rw [CoreObservationGraph.outMoment_eq_average _ y hr hb hy hZ hlam]
  exact coreLawAverage_empty _ _

end CoreObservationEnsemble

end CoulombAtom

end

end OAI
