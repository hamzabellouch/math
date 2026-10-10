import Mathlib
import OAI.Analysis.CoulombIonization.Fermionic.QuantumEventMultiplier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumMultiplierLaw_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom

lemma finite_product_integral {α ι κ : Type*} [MeasurableSpace α] [Fintype ι] [Fintype κ]
    (μ : Measure α) (f : ι → α → ℝ) (g : κ → α → ℝ)
    (hi : ∀ i k, Integrable (fun x => f i x * g k x) μ) :
    (∑ k, ∑ i, ∫ x, f i x * g k x ∂μ) =
      ∫ x, (∑ k, g k x) * (∑ i, f i x) ∂μ := by
  have he (x : α) : (∑ k, g k x) * (∑ i, f i x) = ∑ k, ∑ i, f i x * g k x := by
    rw [sum_mul]
    simp only [mul_sum]
    apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [he]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun i _ => hi i k))]
  apply sum_congr rfl
  intro k _
  exact (integral_finsetSum _ (fun i _ => hi i k)).symm

attribute [local irreducible] graphComponent fermionGraphValue FermionLipschitzMultiplier.apply

lemma FermionLipschitzMultiplier.apply_rawDensity {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    graphRawDensity (p.apply F) =ᵐ[volume] fun x => (p.value x)^2 * graphRawDensity F x := by
  have ha : ∀ᵐ x, ∀ s : Spins N,
      graphComponent s none (p.apply F) x = (p.value x : ℂ) * graphComponent s none F x :=
    ae_all_iff.mpr (fun s => p.apply_value F s)
  filter_upwards [ha] with x hx
  simp only [graphRawDensity, hx, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, mul_sum]

lemma FermionLipschitzMultiplier.apply_rawLaw {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    graphRawLaw (p.apply F) = (graphRawLaw F).withDensity (fun x => ENNReal.ofReal ((p.value x)^2)) := by
  unfold graphRawLaw
  rw [← withDensity_mul volume (graphRawDensity_measurable F).ennreal_ofReal
    (p.lipschitz.continuous.measurable.pow_const 2).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [p.apply_rawDensity F] with x hx
  rw [hx, ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_comm _ _

lemma FermionLipschitzMultiplier.apply_norm_sq {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    ‖fermionGraphValue N (p.apply F)‖^2 = ∫ x, (p.value x)^2 ∂graphRawLaw F := by
  rw [← graphRawDensity_integral, graphRawLaw_integral]
  apply integral_congr_ae
  filter_upwards [p.apply_rawDensity F] with x hx
  exact hx.trans (mul_comm _ _)

lemma FermionLipschitzMultiplier.deriv_component_integrable {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N)
    (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => (lineDeriv ℝ p.value x (direction i a))^2 *
      ‖graphComponent s none F x‖^2) := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable
    (graphComponent s none F))).mp (Lp.memLp _)
  have hb (x : Configuration N) :
      ‖(lineDeriv ℝ p.value x (direction i a))^2‖ ≤ (p.constant * ‖direction i a‖)^2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hd := norm_lineDeriv_le_of_lipschitz ℝ p.lipschitz (x₀ := x) (v := direction i a)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hd 2
  exact hi.bdd_mul ((measurable_lineDeriv p.lipschitz.continuous).pow_const 2).aestronglyMeasurable
    (ae_of_all _ hb)

lemma FermionLipschitzMultiplier.gradient_rawLaw {N : ℕ}
    (p : FermionLipschitzMultiplier N) (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x, (lineDeriv ℝ p.value x (direction i a))^2 * ‖graphComponent s none F x‖^2) =
    ∫ x, ∑ q : Fin N × Fin 3, (lineDeriv ℝ p.value x (direction q.1 q.2))^2
      ∂graphRawLaw F := by
  rw [graphRawLaw_integral]
  have hh := finite_product_integral volume
    (fun (q : Fin N × Fin 3) (x : Configuration N) =>
      (lineDeriv ℝ p.value x (direction q.1 q.2))^2)
    (fun (s : Spins N) (x : Configuration N) => ‖graphComponent s none F x‖^2)
    (fun q s => p.deriv_component_integrable F s q.1 q.2)
  simpa only [graphRawDensity, Fintype.sum_prod_type] using hh

end CoulombAtom

end Work_QuantumMultiplierLaw_scope

section Work_EventPosterior_scope

open MeasureTheory Set
open scoped ENNReal

namespace CoulombObservation

lemma event_raw_marginal {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    Measure.map Prod.fst ((μ.prod ν).restrict A) =
      μ.withDensity (fun x => ν (Prod.mk x ⁻¹' A)) := by
  ext t ht
  rw [Measure.map_apply measurable_fst ht, Measure.restrict_apply (measurable_fst ht),
    Measure.prod_apply ((measurable_fst ht).inter hA), withDensity_apply _ ht,
    ← lintegral_indicator ht]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ t
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' t ∩ A) = Prod.mk x ⁻¹' A := by
      ext y
      simp [hx]
    rw [he, indicator_of_mem hx]
  · have he : Prod.mk x ⁻¹' (Prod.fst ⁻¹' t ∩ A) = ∅ := by
      ext y
      simp [hx]
    rw [he, measure_empty, indicator_of_notMem hx]

lemma event_probability_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    {A : Set (α × β)} (hA : MeasurableSet A) :
    (μ.prod ν) A = ∫⁻ x, ν (Prod.mk x ⁻¹' A) ∂μ :=
  Measure.prod_apply hA

end CoulombObservation

end Work_EventPosterior_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators

namespace CoulombAtom
open CoulombObservation

def quantumObservationEvent {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) (s : Set (J × (Fin N × Fin 3) → ℝ)) :
    Set (Configuration N × (J × (Fin N × Fin 3) → ℝ)) :=
  {z | observationPlacement b (flattenConfiguration N z.1) + z.2 ∈ s}

lemma quantumObservationEvent_measurable {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (quantumObservationEvent b s) := by
  apply hs.preimage
  exact (((observationPlacement b).measurable.comp (flattenConfiguration N).measurable).comp
    measurable_fst).add measurable_snd

lemma quantumEventLikelihood_ofReal {N : ℕ} {J : Type*} [Fintype J]
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s)
    (x : Configuration N) :
    ENNReal.ofReal (quantumEventLikelihood b s x) =
      (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))
        (Prod.mk x ⁻¹' quantumObservationEvent b s) := by
  unfold quantumEventLikelihood
  rw [arrayLikelihood_eq_probability b hs]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma quantumEventProbability_ofReal {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (hn : ‖fermionGraphValue N F‖^2 = 1)
    (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)} (hs : MeasurableSet s) :
    ENNReal.ofReal (quantumEventProbability F b s) =
      ((graphRawLaw F).prod (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw)))
        (quantumObservationEvent b s) := by
  let := graphRawLaw_probability F hn
  have hi := integrable_bounded_probability (μ := graphRawLaw F)
    (quantumEventLikelihood_measurable b hs) (quantumEventLikelihood_nonneg b hs)
    (quantumEventLikelihood_le_one b hs)
  rw [quantumEventProbability, ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (quantumEventLikelihood_nonneg b hs)),
    Measure.prod_apply (quantumObservationEvent_measurable b hs)]
  exact lintegral_congr (quantumEventLikelihood_ofReal b hs)

lemma quantumEventMultiplier_rawLaw {N : ℕ} {J : Type*} [Fintype J]
    (F : fermionGraph N) (b : J → ℝ) {s : Set (J × (Fin N × Fin 3) → ℝ)}
    (hs : MeasurableSet s) (hsy : QuantumEventSymmetric s)
    (hp : 0 < quantumEventProbability F b s) :
    graphRawLaw ((quantumEventMultiplier b hs hsy (quantumEventProbability F b s)).apply F) =
      (ENNReal.ofReal (quantumEventProbability F b s))⁻¹ •
        Measure.map Prod.fst
          (((graphRawLaw F).prod
            (Measure.pi (fun _ : J × (Fin N × Fin 3) => compactNoiseLaw))).restrict
              (quantumObservationEvent b s)) := by
  rw [FermionLipschitzMultiplier.apply_rawLaw,
    event_raw_marginal _ _ (quantumObservationEvent_measurable b hs)]
  simp only [quantumEventMultiplier_sq b hs hsy hp,
    ENNReal.ofReal_mul (inv_nonneg.mpr hp.le), ENNReal.ofReal_inv_of_pos hp,
    ← quantumEventLikelihood_ofReal b hs]
  exact withDensity_smul _ (quantumEventLikelihood_measurable b hs).ennreal_ofReal

end CoulombAtom

end

end OAI
