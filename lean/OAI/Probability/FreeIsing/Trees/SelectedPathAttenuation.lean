import OAI.Probability.FreeIsing.Conditioning.Attenuation
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Trees.ConeSelectedFieldAttenuation
import OAI.Probability.FreeIsing.Trees.SelectedPathLocality

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

def forwardGaussianField {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (t : ℝ≥0) (v : TreeVertex d) (k : ℕ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : ℝ :=
  Real.artanh (selectedPosterior
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
    (fun s z => (t : ℝ) * spinSign s + z)
    (Subtype.val : cone (ConnectedHull.takeVertex v (k + 1)) → TreeVertex d)
    (ConnectedHull.takeVertex v (k + 1)) p)

theorem measurable_forwardGaussianField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) (k : ℕ) :
    Measurable (forwardGaussianField μ t v k) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  exact ha.comp (measurable_selectedPosterior _
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) _ _)

theorem measurable_later_forwardGaussianField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (hd : 3 ≤ d) (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    Measurable[noisyRegionSigma (A := ℝ) (cone (sideVertex hd v i))ᶜ]
      (forwardGaussianField μ t v j) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  apply ha.comp
  exact measurable_later_selectedPosterior _
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) hd v hij _

theorem integral_forwardGaussianField_attenuation_le_exp_of_condExp
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (hθ : theta ^ 2 ≤ 1)
    (hd : 3 ≤ d) (t : ℝ≥0) (v : TreeVertex d) {delta : ℝ} (hδ : delta ≤ 1)
    (hCE : ∀ i : Fin v.1.length,
      ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[
          fun p => responseAttenuation theta (forwardGaussianField μ t v i p) ^ 2 |
          noisyRegionSigma (A := ℝ) (cone (sideVertex hd v i))ᶜ]) p ≤ 1 - delta) :
    (∫ p, ∏ k ∈ Finset.range v.1.length,
      responseAttenuation theta (forwardGaussianField μ t v k p) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-delta * (v.1.length : ℝ)) := by
  classical
  let A : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
    fun k p => responseAttenuation theta (forwardGaussianField μ t v k p) ^ 2
  let m : ℕ → MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun k => if hk : k < v.1.length then
      noisyRegionSigma (A := ℝ) (cone (sideVertex hd v ⟨k, hk⟩))ᶜ else ⊥
  have hresp : Measurable (fun z : ℝ => responseAttenuation theta z ^ 2) :=
    (continuous_responseAttenuation hθ).measurable.pow_const 2
  have hMeas (k : ℕ) : Measurable (A k) :=
    hresp.comp (measurable_forwardGaussianField μ t v k)
  have hBound (k : ℕ) (p) : 0 ≤ A k p ∧ A k p ≤ 1 := by
    have hp := responseAttenuation_pos hθ (forwardGaussianField μ t v k p)
    have hl := responseAttenuation_le_one hθ (forwardGaussianField μ t v k p)
    exact ⟨sq_nonneg _, by dsimp [A]; nlinarith⟩
  have hm (k : ℕ) (hk : k ∈ Finset.range v.1.length) : m k ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) := by
    simp only [Finset.mem_range] at hk
    simpa only [m, dite_eq_left hk] using
      noisyRegionSigma_le (A := ℝ) (cone (sideVertex hd v ⟨k, hk⟩))ᶜ
  have hcond (k : ℕ) (hk : k ∈ Finset.range v.1.length) :
      ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[A k | m k]) p ≤
          1 - delta := by
    simp only [Finset.mem_range] at hk
    simpa only [m, dite_eq_left hk, A] using hCE ⟨k, hk⟩
  have hLater (i : ℕ) (hi : i ∈ Finset.range v.1.length)
      (j : ℕ) (hj : j ∈ Finset.range v.1.length) (hij : i < j) :
      Measurable[m i] (A j) := by
    simp only [Finset.mem_range] at hi hj
    have hmi : m i = noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi⟩))ᶜ := by simp only [m, dite_eq_left hi]
    have ht : Measurable[noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi⟩))ᶜ] (A j) := by
      exact hresp.comp (measurable_later_forwardGaussianField μ t hd v
        (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    exact hmi.symm ▸ ht
  simpa only [Finset.card_range, A] using
    integral_prod_le_exp_of_condExp_le hδ A m (Finset.range v.1.length)
      (fun k _ => hMeas k) (fun k _ => hBound k) hm hcond hLater

theorem integral_forwardGaussianField_attenuation_le_exp_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    (∫ p, ∏ k ∈ Finset.range v.1.length,
      responseAttenuation (Real.tanh beta) (forwardGaussianField μ t v k p) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1) * (v.1.length : ℝ)) := by
  let := hμ.isProbabilityMeasure
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hc := ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1
  have hc1 := ComponentSignalAttenuation.lossCoefficient_le_half (Real.tanh beta)
  have hδ : ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
      min (Real.sqrt (t : ℝ)) 1 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (Real.sqrt (t : ℝ)) (1 : ℝ)) hc.le
    nlinarith
  apply integral_forwardGaussianField_attenuation_le_exp_of_condExp
    (by nlinarith : Real.tanh beta ^ 2 ≤ 1) hd t v hδ
  intro i
  have hr : (sideVertex hd v i).1 ≠ [] := by
    intro he
    have hl := sideVertex_length hd v i
    rw [he] at hl
    simp at hl
  have hp : parentVertex (sideVertex hd v i) ∈ reducedForward hd v i := by
    rw [parent_sideVertex]
    exact target_mem_reducedForward hd v i
  have h := hμ.condExp_selected_cone_field_attenuation_le_critical
    hbeta hθ0 hcritical ht (sideVertex hd v i) hr (reducedForward hd v i)
    (reducedForward_subset_complement hd v i) hp
  have hfield := forwardObservationField_eq_reduced_sup_side
    (fun s z => (t : ℝ) * spinSign s + z) hd v i
  rw [← selectedObservationField_region_union] at hfield
  simpa only [parent_sideVertex, selectedPosterior, ← hfield,
    forwardGaussianField] using h

end Problem367.PathSideBranches

end

end OAI
