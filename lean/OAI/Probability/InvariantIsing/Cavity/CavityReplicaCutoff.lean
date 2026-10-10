import OAI.Probability.InvariantIsing.Cavity.CavityCutoffTests
import OAI.Probability.InvariantIsing.Cavity.CavityDisorderMean

namespace OAI

/-! Explicit normalization of a cutoff in a bounded two-replica test.
The ratio convention also covers an empty cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

def cavityCutoffReplicaMean {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (H : X → ℝ) (s : Set X) (F : (Fin 2 → X) → ℝ) : ℝ :=
  referenceReplicaMean ν H (fun σ => if ∀ i, σ i ∈ s then F σ else 0) /
    referenceReplicaMean ν H (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then 1 else 0)

lemma measurable_cavityCutoffReplicaMean {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (H : Ω × X → ℝ) (hH : Measurable H) (s : Ω → Set X)
    (hs : MeasurableSet {p : Ω × X | p.2 ∈ s p.1})
    (F : Ω × (Fin 2 → X) → ℝ) (hF : Measurable F) :
    Measurable (fun ω => cavityCutoffReplicaMean ν (fun x => H (ω, x)) (s ω)
      (fun σ => F (ω, σ))) := by
  have hS : MeasurableSet {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} := by
    have he : {p : Ω × (Fin 2 → X) | ∀ i, p.2 i ∈ s p.1} =
        ⋂ i, {p : Ω × (Fin 2 → X) | p.2 i ∈ s p.1} := by ext p; simp
    rw [he]
    exact MeasurableSet.iInter (fun i => hs.preimage
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  exact (measurable_referenceReplicaMean ν (H := H) hH
    (Measurable.ite hS hF measurable_const)).div
      (measurable_referenceReplicaMean ν (H := H) hH
        (Measurable.ite hS measurable_const measurable_const))

lemma cavity_cutoff_replica_eq_cond {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ) :
    cavityCutoffReplicaMean ν H s F =
      ∫ σ, F σ ∂cond (Measure.pi (fun _ : Fin 2 => ν.tilted H))
        (univ.pi (fun _ => s)) := by
  let P := Measure.pi (fun _ : Fin 2 => ν.tilted H)
  let S := univ.pi (fun _ : Fin 2 => s)
  have hS : MeasurableSet S := MeasurableSet.univ_pi (fun _ => hs)
  have hnum : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then F σ else 0) = S.indicator F := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  have hden : (fun σ : Fin 2 → X => if ∀ i, σ i ∈ s then (1 : ℝ) else 0) =
      S.indicator (fun _ => (1 : ℝ)) := by
    funext σ
    simp only [S, mem_univ_pi, indicator_apply]
  rw [cavityCutoffReplicaMean, referenceReplicaMean_eq_tilted ν H hH,
    referenceReplicaMean_eq_tilted ν H hH, hnum, hden]
  change (∫ σ, S.indicator F σ ∂P) / (∫ σ, S.indicator (fun _ => (1 : ℝ)) σ ∂P) = _
  rw [integral_indicator hS, integral_indicator hS, integral_const]
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [smul_eq_mul, ENNReal.toReal_inv, Measure.real, Measure.restrict_apply_univ, mul_one, div_eq_inv_mul]
  rfl

theorem cavity_cutoff_replica_error {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) (F : (Fin 2 → X) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hF : ∀ σ, |F σ| ≤ M) :
    |cavityCutoffReplicaMean ν H s F - referenceReplicaMean ν H F| ≤
      4 * M * (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted hH
  rw [cavity_cutoff_replica_eq_cond ν H hH s hs F, referenceReplicaMean_eq_tilted ν H hH]
  exact cavity_twoReplica_cutoff_bound (ν.tilted H) s hs F
    (Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable M
      (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hF σ)) hM hF

lemma cavity_reference_tail_eq {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (H : X → ℝ)
    (hH : Integrable (fun x => Real.exp (H x)) ν)
    (s : Set X) (hs : MeasurableSet s) :
    referenceReplicaMean ν H (fun σ : Fin 2 → X => if σ 0 ∈ sᶜ then 1 else 0) =
      (ν.tilted H).real sᶜ := by
  let := isProbabilityMeasure_tilted hH
  rw [referenceReplicaMean_eq_tilted ν H hH]
  have he : (fun σ : Fin 2 → X => if σ 0 ∈ sᶜ then (1 : ℝ) else 0) =
      fun σ => (sᶜ).indicator (fun _ : X => (1 : ℝ)) (σ 0) := by
    funext σ
    simp only [indicator_apply]
  rw [he, integral_comp_eval]
  · rw [integral_indicator hs.compl, integral_const]
    simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
  · exact (measurable_const.indicator hs.compl).aestronglyMeasurable

end InvariantIsing

end

end OAI
