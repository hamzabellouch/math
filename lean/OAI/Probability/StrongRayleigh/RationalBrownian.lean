import OAI.Probability.StrongRayleigh.StandardBorelCountable

namespace OAI

universe u_1

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem336AdditiveD139.RationalBrownian

variable {I : Type u_1}

def sampleImage (time : I → ℝ≥0) (S : Finset I)
    (x : S.image time → ℝ) : S → ℝ :=
  fun i => x ⟨time i, Finset.mem_image_of_mem time i.property⟩

lemma measurable_sampleImage (time : I → ℝ≥0) (S : Finset I) :
    Measurable (sampleImage time S) := by
  fun_prop [sampleImage]

def finiteLaw (time : I → ℝ≥0) (S : Finset I) : Measure (S → ℝ) :=
  (BrownianReal.projectiveFamily (S.image time)).map (sampleImage time S)

instance finiteLaw_isProbabilityMeasure (time : I → ℝ≥0) (S : Finset I) :
    IsProbabilityMeasure (finiteLaw time S) := by
  unfold finiteLaw
  infer_instance

lemma sampleImage_hasLaw (time : I → ℝ≥0) (S : Finset I) :
    HasLaw (sampleImage time S) (finiteLaw time S)
      (BrownianReal.projectiveFamily (S.image time)) :=
  ⟨(measurable_sampleImage time S).aemeasurable, rfl⟩

theorem finiteLaw_projective (time : I → ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun _ : I => ℝ) (finiteLaw time) := by
  classical
  intro S T hTS
  have himage : T.image time ⊆ S.image time := Finset.image_subset_image hTS
  unfold finiteLaw
  rw [BrownianReal.isProjectiveMeasureFamily_projectiveFamily
    (S.image time) (T.image time) himage]
  rw [Measure.map_map (measurable_sampleImage time T)
    (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => ℝ) himage),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : I => ℝ) hTS) (measurable_sampleImage time S)]
  congr 1

theorem finiteLaw_eval_hasLaw (time : I → ℝ≥0) (S : Finset I) (i : S) :
    HasLaw (fun x : S → ℝ => x i) (gaussianReal 0 (time i)) (finiteLaw time S) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  unfold finiteLaw
  rw [Measure.map_map (by fun_prop) (measurable_sampleImage time S)]
  exact (BrownianReal.measurePreserving_eval_projectiveFamily
    (I := S.image time) ⟨time i, Finset.mem_image_of_mem time i.property⟩).map_eq

theorem finiteLaw_increment_hasLaw (time : I → ℝ≥0) (S : Finset I) (i j : S) :
    HasLaw (fun x : S → ℝ => x i - x j)
      (gaussianReal 0 (nndist (time i) (time j))) (finiteLaw time S) := by
  refine ⟨by fun_prop, ?_⟩
  unfold finiteLaw
  rw [Measure.map_map (by fun_prop) (measurable_sampleImage time S)]
  exact (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily (S.image time)
    ⟨time i, Finset.mem_image_of_mem time i.property⟩
    ⟨time j, Finset.mem_image_of_mem time j.property⟩).map_eq

instance finiteLaw_isGaussian (time : I → ℝ≥0) (S : Finset I) :
    IsGaussian (finiteLaw time S) := by
  let L : (S.image time → ℝ) →L[ℝ] (S → ℝ) :=
    ContinuousLinearMap.pi fun i =>
      ContinuousLinearMap.proj ⟨time i, Finset.mem_image_of_mem time i.property⟩
  have h := (IsGaussian.hasGaussianLaw_id
    (μ := BrownianReal.projectiveFamily (S.image time))).map L
  exact h.isGaussian_map

lemma finiteLaw_eval_mean (time : I → ℝ≥0) (S : Finset I) (i : S) :
    (∫ x, x i ∂finiteLaw time S) = 0 := by
  rw [(finiteLaw_eval_hasLaw time S i).integral_eq, integral_id_gaussianReal]

lemma finiteLaw_eval_covariance (time : I → ℝ≥0) (S : Finset I) (i j : S) :
    cov[fun x => x i, fun x => x j; finiteLaw time S] = min (time i) (time j) := by
  rw [← (sampleImage_hasLaw time S).covariance_fun_comp
    (f := fun x => x i) (g := fun x => x j)
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable]
  exact BrownianReal.covariance_eval_projectiveFamily _ _ _

theorem projectiveLimit_hasLaw {time : I → ℝ≥0} {ν : Measure (I → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : I => ℝ) ν (finiteLaw time)) (S : Finset I) :
    HasLaw S.restrict (finiteLaw time S) ν :=
  ⟨(Finset.measurable_restrict S).aemeasurable, hν S⟩

theorem projectiveLimit_isGaussianProcess {time : I → ℝ≥0} {ν : Measure (I → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : I => ℝ) ν (finiteLaw time)) :
    IsGaussianProcess (fun i (x : I → ℝ) => x i) ν where
  hasGaussianLaw S := (projectiveLimit_hasLaw hν S).hasGaussianLaw

theorem projectiveLimit_increment_hasLaw {time : I → ℝ≥0} {ν : Measure (I → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : I => ℝ) ν (finiteLaw time)) (i j : I) :
    HasLaw (fun x : I → ℝ => x i - x j)
      (gaussianReal 0 (nndist (time i) (time j))) ν := by
  classical
  exact (finiteLaw_increment_hasLaw time {i, j} ⟨i, by simp⟩ ⟨j, by simp⟩).comp
    (projectiveLimit_hasLaw hν {i, j})

theorem projectiveLimit_eval_hasLaw {time : I → ℝ≥0} {ν : Measure (I → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : I => ℝ) ν (finiteLaw time)) (i : I) :
    HasLaw (fun x : I → ℝ => x i) (gaussianReal 0 (time i)) ν := by
  classical
  exact (finiteLaw_eval_hasLaw time {i} ⟨i, by simp⟩).comp
    (projectiveLimit_hasLaw hν {i})

theorem projectiveLimit_covariance {time : I → ℝ≥0} {ν : Measure (I → ℝ)}
    (hν : IsProjectiveLimit (α := fun _ : I => ℝ) ν (finiteLaw time)) (i j : I) :
    cov[fun x => x i, fun x => x j; ν] = min (time i) (time j) := by
  classical
  calc
    _ = cov[fun x => x (⟨i, by simp⟩ : ({i, j} : Finset I)),
        fun x => x (⟨j, by simp⟩ : ({i, j} : Finset I)); finiteLaw time {i, j}] :=
      (projectiveLimit_hasLaw hν {i, j}).covariance_fun_comp
        (f := fun x => x ⟨i, by simp⟩) (g := fun x => x ⟨j, by simp⟩)
        (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
    _ = _ := finiteLaw_eval_covariance time {i, j} _ _

theorem exists_nat_law (time : ℕ → ℝ≥0) :
    ∃ ν : ProbabilityMeasure (ℕ → ℝ),
      IsProjectiveLimit (α := fun _ : ℕ => ℝ) (ν : Measure (ℕ → ℝ)) (finiteLaw time) := by
  have hstep (n : ℕ) :
      (finiteLaw time (Finset.Iic (n + 1))).map
        (Preorder.frestrictLe₂ (π := fun _ => ℝ) n.le_succ) =
      finiteLaw time (Finset.Iic n) :=
    (finiteLaw_projective time _ _ (Finset.Iic_subset_Iic.mpr n.le_succ)).symm
  obtain ⟨ν, hν⟩ := StandardBorelProjective.exists_probabilityMeasure_prefix
    (fun n => ⟨finiteLaw time (Finset.Iic n), inferInstance⟩) hstep
  exact ⟨ν, (isProjectiveLimit_nat_iff (finiteLaw_projective time) _).2 hν⟩

theorem exists_countable_law [Countable I] (time : I → ℝ≥0) :
    ∃ ν : ProbabilityMeasure (I → ℝ),
      IsProjectiveLimit (α := fun _ : I => ℝ) (ν : Measure (I → ℝ)) (finiteLaw time) :=
  StandardBorelProjective.exists_projectiveLimit_countable
    (finiteLaw time) (finiteLaw_projective time)

theorem exists_countable_process [Countable I] (time : I → ℝ≥0) :
    ∃ ν : ProbabilityMeasure (ℕ → ℝ), ∃ X : I → (ℕ → ℝ) → ℝ,
      (∀ i, Measurable (X i)) ∧ IsGaussianProcess X (ν : Measure (ℕ → ℝ)) ∧
      (∀ i, HasLaw (X i) (gaussianReal 0 (time i)) (ν : Measure (ℕ → ℝ))) ∧
      (∀ i j, HasLaw (fun x => X i x - X j x)
        (gaussianReal 0 (nndist (time i) (time j))) (ν : Measure (ℕ → ℝ))) ∧
      (∀ i j, cov[X i, X j; (ν : Measure (ℕ → ℝ))] = min (time i) (time j)) := by
  classical
  let : Encodable I := Encodable.ofCountable I
  let timeN : ℕ → ℝ≥0 := fun n => (Encodable.decode (α := I) n).elim 0 time
  have htime (i : I) : timeN (Encodable.encode i) = time i := by
    simp [timeN]
  obtain ⟨ν, hν⟩ := exists_nat_law timeN
  let X : I → (ℕ → ℝ) → ℝ := fun i x => x (Encodable.encode i)
  refine ⟨ν, X, fun i => measurable_pi_apply _, ?_, ?_, ?_, ?_⟩
  · exact (projectiveLimit_isGaussianProcess hν).comp_right Encodable.encode
  · intro i
    simpa only [htime] using projectiveLimit_eval_hasLaw hν (Encodable.encode i)
  · intro i j
    simpa only [htime] using projectiveLimit_increment_hasLaw hν
      (Encodable.encode i) (Encodable.encode j)

  · intro i j
    simpa only [htime] using projectiveLimit_covariance hν
      (Encodable.encode i) (Encodable.encode j)

end Problem336AdditiveD139.RationalBrownian

end

end OAI
