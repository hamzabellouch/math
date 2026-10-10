import OAI.Probability.SpanningForest.CountableProjective

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Problem336.CountableBrownian

open BrownianReal

def pullbackTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    ((I.image τ) → ℝ) → (I → ℝ) :=
  fun x i => x ⟨τ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩

@[fun_prop]
lemma measurable_pullbackTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    Measurable (pullbackTimes τ I) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply _)

def family (τ : ℕ → ℝ≥0) (I : Finset ℕ) : Measure (I → ℝ) :=
  (projectiveFamily (I.image τ)).map (pullbackTimes τ I)

instance family_probability (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsProbabilityMeasure (family τ I) := by
  unfold family
  infer_instance

instance family_isGaussian (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsGaussian (family τ I) := by
  let L : ((I.image τ) → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
      ⟨τ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩)
  have h : HasGaussianLaw (pullbackTimes τ I) (projectiveFamily (I.image τ)) :=
    (IsGaussian.hasGaussianLaw_id (μ := projectiveFamily (I.image τ))).map L
  exact h.isGaussian_map

lemma family_projective (τ : ℕ → ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun _ : ℕ => ℝ) (family τ) := by
  classical
  intro I J hJI
  unfold family
  rw [isProjectiveMeasureFamily_projectiveFamily (I.image τ) (J.image τ)
    (Finset.image_subset_image hJI)]
  rw [Measure.map_map (measurable_pullbackTimes τ J)
      (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => ℝ) (Finset.image_subset_image hJI)),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℕ => ℝ) hJI) (measurable_pullbackTimes τ I)]
  congr 1

theorem exists_countable_brownian_law (τ : ℕ → ℝ≥0) :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
      IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ) :=
  CountableProjective.exists_projectiveLimit (family τ) (family_projective τ)

theorem hasLaw_increment {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i j : ℕ) :
    HasLaw (fun ω => ω i - ω j) (gaussianReal 0 (nndist (τ i) (τ j))) μ := by
  classical
  let I : Finset ℕ := {i, j}
  let a : I := ⟨i, by simp [I]⟩
  let b : I := ⟨j, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  have hD : HasLaw (fun x => pullbackTimes τ I x a - pullbackTimes τ I x b)
      (gaussianReal 0 (nndist (τ i) (τ j))) (projectiveFamily (I.image τ)) :=
    (measurePreserving_eval_sub_eval_projectiveFamily (I.image τ)
      ⟨τ i, Finset.mem_image.mpr ⟨i, by simp [I], rfl⟩⟩
      ⟨τ j, Finset.mem_image.mpr ⟨j, by simp [I], rfl⟩⟩).hasLaw
  exact HasLaw.comp_of_hasLaw_comp (f := fun x : I → ℝ => x a - x b)
    (by fun_prop) hX hY hD

theorem hasLaw_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i : ℕ) :
    HasLaw (fun ω => ω i) (gaussianReal 0 (τ i)) μ := by
  classical
  let I : Finset ℕ := {i}
  let a : I := ⟨i, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  have hE : HasLaw (fun x => pullbackTimes τ I x a)
      (gaussianReal 0 (τ i)) (projectiveFamily (I.image τ)) :=
    (measurePreserving_eval_projectiveFamily
      ⟨τ i, Finset.mem_image.mpr ⟨i, by simp [I], rfl⟩⟩).hasLaw
  exact HasLaw.comp_of_hasLaw_comp (f := fun x : I → ℝ => x a)
    (measurable_pi_apply a).aemeasurable hX hY hE

theorem isGaussianProcess {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) :
    IsGaussianProcess (fun i ω => ω i) μ where
  hasGaussianLaw I :=
    (show HasLaw I.restrict (family τ I) μ from
      ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩).hasGaussianLaw

lemma integral_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i : ℕ) :
    ∫ ω, ω i ∂μ = 0 := by
  rw [(hasLaw_eval hμ i).integral_eq, integral_id_gaussianReal]

lemma covariance_eval {τ : ℕ → ℝ≥0} {μ : Measure (ℕ → ℝ)}
    (hμ : IsProjectiveLimit (α := fun _ : ℕ => ℝ) μ (family τ)) (i j : ℕ) :
    cov[fun ω => ω i, fun ω => ω j; μ] = min (τ i : ℝ) (τ j : ℝ) := by
  classical
  let I : Finset ℕ := {i, j}
  let a : I := ⟨i, by simp [I]⟩
  let b : I := ⟨j, by simp [I]⟩
  have hX : HasLaw (pullbackTimes τ I) (family τ I)
      (projectiveFamily (I.image τ)) :=
    ⟨(measurable_pullbackTimes τ I).aemeasurable, rfl⟩
  have hY : HasLaw I.restrict (family τ I) μ :=
    ⟨(Finset.measurable_restrict I).aemeasurable, hμ I⟩
  calc
    cov[fun ω => ω i, fun ω => ω j; μ] =
        cov[fun x : I → ℝ => x a, fun x : I → ℝ => x b; family τ I] :=
      hY.covariance_fun_comp (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable
    _ = cov[fun x => pullbackTimes τ I x a, fun x => pullbackTimes τ I x b;
        projectiveFamily (I.image τ)] :=
      (hX.covariance_fun_comp (measurable_pi_apply a).aemeasurable
        (measurable_pi_apply b).aemeasurable).symm
    _ = min (τ i : ℝ) (τ j : ℝ) := covariance_eval_projectiveFamily _ _ _

end Problem336.CountableBrownian

end

end OAI
