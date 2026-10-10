import OAI.GroupTheory.PolycyclicRecognition.Algebra.AutocorrelationLowerBound

namespace OAI

/-! # One quantitative step of backward recurrence -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

/-- Probability of returning to `A` after a difference of two independent
increments with law `σ`. -/
def twoSampleReturn (σ : Measure G) (A : Set G) (x : G) : ℝ≥0∞ :=
  ∫⁻ s₁, ∫⁻ s₂, A.indicator (fun _ => (1 : ℝ≥0∞)) (x * s₁ * s₂⁻¹) ∂σ ∂σ

theorem measurable_twoSampleReturn (σ : Measure G) [SFinite σ]
    {A : Set G} (hA : MeasurableSet A) : Measurable (twoSampleReturn σ A) := by
  have hchi : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hA
  have hm := measurable_rightInverseAverage σ hchi
  exact Measurable.lintegral_prod_right (f := fun x s : G =>
    rightInverseAverage σ (A.indicator (fun _ => (1 : ℝ≥0∞))) (x * s))
    (hm.comp (measurable_fst.mul measurable_snd))

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem twoSampleReturn_le_one (σ : Measure G) [IsProbabilityMeasure σ]
    (A : Set G) (x : G) : twoSampleReturn σ A x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : G, ∫⁻ _ : G, (1 : ℝ≥0∞) ∂σ ∂σ := by
      apply lintegral_mono
      intro s
      apply lintegral_mono
      intro t
      exact indicator_le_self' (fun _ _ => bot_le) _
    _ = 1 := by simp

/-- Discarding points with small return probability retains a definite
quadratic fraction of the original set. This is the backward construction
used to keep every intermediate sheet in the prescribed good set. -/
theorem exists_backward_recurrence_step
    (μ σ : Measure G) [SFinite μ] [IsProbabilityMeasure σ] [μ.IsMulRightInvariant]
    (A Q K R : Set G) (hA : MeasurableSet A) (hQfin : μ Q ≠ ∞)
    (hAQ : A ⊆ Q) (hApos : 0 < (μ A).toReal) (hQpos : 0 < (μ Q).toReal)
    (hK : ∀ᵐ s ∂σ, s ∈ K) (hRfin : μ R ≠ ∞) (hRpos : 0 < (μ R).toReal)
    (hAR : ∀ a ∈ A, ∀ s ∈ K, a * s ∈ R)
    {D : ℝ} (hD : 0 < D) (hvol : (μ R).toReal ≤ D * (μ Q).toReal) :
    ∃ B : Set G, MeasurableSet B ∧ B ⊆ A ∧ 0 < (μ B).toReal ∧
      (μ A).toReal ^ 2 / (2 * D * (μ Q).toReal) ≤ (μ B).toReal ∧
      ∀ x ∈ B, (μ A).toReal / (2 * D * (μ Q).toReal) ≤
        (twoSampleReturn σ A x).toReal := by
  let ν := μ.restrict A
  have hAfin : μ A ≠ ∞ := (lt_of_le_of_lt (measure_mono hAQ) hQfin.lt_top).ne
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hAfin.lt_top⟩
  let p : G → ℝ := fun x => (twoSampleReturn σ A x).toReal
  have hpm : Measurable p := (measurable_twoSampleReturn σ hA).ennreal_toReal
  have hp (x : G) : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, by simpa using ENNReal.toReal_mono (by simp) (twoSampleReturn_le_one σ A x)⟩
  have hI : (∫ x, p x ∂ν) = (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal := by
    exact integral_toReal (measurable_twoSampleReturn σ hA).aemeasurable
      (Eventually.of_forall (fun x => (twoSampleReturn_le_one σ A x).trans_lt (by simp)))
  have hlow : (μ A).toReal ^ 2 ≤ (D * (μ Q).toReal) * ∫ x, p x ∂ν := by
    have h := return_correlation_lower_bound μ σ A K R hA hK hRfin hRpos hAR
    change (μ A).toReal ^ 2 ≤ (μ R).toReal *
      (∫⁻ x in A, twoSampleReturn σ A x ∂μ).toReal at h
    rw [← hI] at h
    exact h.trans (mul_le_mul_of_nonneg_right hvol (integral_nonneg (fun x => (hp x).1)))
  let M := D * (μ Q).toReal
  have hM : 0 < M := mul_pos hD hQpos
  let t := (μ A).toReal / (2 * M)
  let B := A ∩ {x | t ≤ p x}
  have hlevel : MeasurableSet {x | t ≤ p x} := measurableSet_le measurable_const hpm
  have hBm : MeasurableSet B := hA.inter hlevel
  have hmass : ν.real {x | t ≤ p x} = (μ B).toReal := by
    simp only [measureReal_def, ν, Measure.restrict_apply hlevel, B, inter_comm]
  have hu := integral_le_superlevel_mass_add ν p hpm hp (div_nonneg hApos.le (by positivity : 0 ≤ 2 * M))
  change (∫ x, p x ∂ν) ≤ ν.real {x | t ≤ p x} + t * ν.real univ at hu
  rw [hmass, show ν.real univ = (μ A).toReal by simp [measureReal_def, ν]] at hu
  have htM : t * M = (μ A).toReal / 2 := by dsimp [t]; field_simp
  have hmul : M * (∫ x, p x ∂ν) ≤ M * (μ B).toReal + (μ A).toReal ^ 2 / 2 := by
    calc
      _ ≤ M * ((μ B).toReal + t * (μ A).toReal) := mul_le_mul_of_nonneg_left hu hM.le
      _ = M * (μ B).toReal + (t * M) * (μ A).toReal := by ring
      _ = _ := by rw [htM]; ring
  have hbnd : (μ A).toReal ^ 2 / (2 * M) ≤ (μ B).toReal := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
    change (μ A).toReal ^ 2 ≤ M * (∫ x, p x ∂ν) at hlow
    nlinarith [hlow, hmul]
  have hBpos : 0 < (μ B).toReal :=
    (div_pos (sq_pos_of_pos hApos) (mul_pos (by norm_num) hM)).trans_le hbnd
  refine ⟨B, hBm, inter_subset_left, hBpos, ?_, ?_⟩
  · simpa only [M, mul_assoc] using hbnd
  · intro x hx
    have hx' : t ≤ p x := hx.2
    simpa only [t, p, M, mul_assoc] using hx'

end PolycyclicRecognition

end

end OAI
