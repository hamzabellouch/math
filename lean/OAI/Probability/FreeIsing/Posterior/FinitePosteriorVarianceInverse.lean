import OAI.Probability.FreeIsing.Posterior.VarianceInverse

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.FinitePosteriorVariance

open PlantedSymmetry

local instance : Nonempty IsingSpin := ⟨.neg⟩

def spinMean {d : ℕ} (beta : ℝ) (D : Finset (TreeVertex d)) (v : D)
    (y : TreeVertex d → ℝ) : ℝ :=
  FinitePosterior.fieldMean (finiteIsingEnergy beta D)
    (fun (eta : D → IsingSpin) w => spinSign (eta w))
    (fun eta => spinSign (eta v)) (D.restrict y)

theorem continuous_spinMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) : Continuous (spinMean beta D v) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun w => continuous_apply w.1)

theorem spinMean_mem_Ioo {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (y : TreeVertex d → ℝ) :
    spinMean beta D v y ∈ Set.Ioo (-1 : ℝ) 1 := by
  exact FinitePosterior.fieldMean_spin_mem_Ioo _ _ _ _
    (fun eta => by cases eta v <;> simp [spinSign])
    ⟨fun _ => .neg, rfl⟩ ⟨fun _ => .pos, rfl⟩

theorem field_sub_observation_abs_le {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v : D) (y : TreeVertex d → ℝ) :
    |Real.artanh (spinMean beta D v y) - y v| ≤ (d : ℝ) * beta := by
  exact finite_tree_gibbs_field_uniform_bound D hbeta (D.restrict y) v

theorem field_abs_le_noise {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    |Real.artanh (spinMean beta D v (observation t p))| ≤
      (d : ℝ) * beta + (t : ℝ) + |p.2 v| := by
  have ho : |observation t p v| ≤ (t : ℝ) + |p.2 v| := by
    calc
      _ ≤ |(t : ℝ) * spinSign (p.1 v)| + |p.2 v| := abs_add_le _ _
      _ = _ := by
        cases hs : p.1 v <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    _ ≤ |Real.artanh (spinMean beta D v (observation t p)) - observation t p v| +
      |observation t p v| := by
        simpa using abs_sub_le (Real.artanh (spinMean beta D v (observation t p)))
          (observation t p v) 0
    _ ≤ (d : ℝ) * beta + ((t : ℝ) + |p.2 v|) :=
      add_le_add (field_sub_observation_abs_le hbeta D v _) ho
    _ = _ := by ring

private theorem measurable_field {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) :
    Measurable (fun p => Real.artanh (spinMean beta D v (observation t p))) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  exact ha.comp ((continuous_spinMean beta D v).measurable.comp (measurable_observation t))

theorem integrable_exp_abs_field {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun p => Real.exp (a * |Real.artanh
      (spinMean beta D v (observation t p))|))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  exact integrable_exp_abs_of_gaussian_bound (measurable_field beta D v t)
    (PlantedInformation.noise_hasLaw μ t v) ha
    (Filter.Eventually.of_forall (field_abs_le_noise hbeta D v t))

theorem integral_exp_abs_field_le {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    (∫ p, Real.exp (a * |Real.artanh (spinMean beta D v (observation t p))|)
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * Real.exp (a * ((d : ℝ) * beta + t) + (t : ℝ) * a ^ 2 / 2) := by
  exact integral_exp_abs_le_of_gaussian_bound (measurable_field beta D v t)
    (PlantedInformation.noise_hasLaw μ t v) ha
    (Filter.Eventually.of_forall (field_abs_le_noise hbeta D v t))

theorem inverse_variance_pow_le_noise {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) (k : ℕ)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    ((1 - (spinMean beta D v (observation t p)) ^ 2)⁻¹) ^ k ≤
      Real.exp ((2 * (k : ℝ)) * ((d : ℝ) * beta + (t : ℝ) + |p.2 v|)) := by
  apply (inverse_spin_variance_pow_le_exp (spinMean_mem_Ioo beta D v _) k).trans
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (field_abs_le_noise hbeta D v t p) (by positivity))

theorem integrable_inverse_variance_pow {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) (k : ℕ) :
    Integrable (fun p => ((1 - (spinMean beta D v (observation t p)) ^ 2)⁻¹) ^ k)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  apply (integrable_exp_abs_field hbeta μ D v t
    (a := 2 * (k : ℝ)) (by positivity)).mono'
  · exact ((measurable_const.sub (((continuous_spinMean beta D v).measurable.comp
      (measurable_observation t)).pow_const 2)).inv.pow_const k).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro p
    have hm := spinMean_mem_Ioo beta D v (observation t p)
    have hpos : 0 < 1 - (spinMean beta D v (observation t p)) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hm.2) (show 0 < 1 + spinMean beta D v
        (observation t p) by linarith [hm.1])]
    rw [Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hpos.le) _)]
    exact inverse_spin_variance_pow_le_exp hm k

theorem integral_inverse_variance_pow_le {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (D : Finset (TreeVertex d)) (v : D) (t : ℝ≥0) (k : ℕ) :
    (∫ p, ((1 - (spinMean beta D v (observation t p)) ^ 2)⁻¹) ^ k
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      2 * Real.exp ((2 * (k : ℝ)) * ((d : ℝ) * beta + t) +
        (t : ℝ) * (2 * (k : ℝ)) ^ 2 / 2) := by
  calc
    _ ≤ ∫ p, Real.exp ((2 * (k : ℝ)) * |Real.artanh
        (spinMean beta D v (observation t p))|)
          ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t) := by
      apply integral_mono (integrable_inverse_variance_pow hbeta μ D v t k)
        (integrable_exp_abs_field hbeta μ D v t (by positivity))
      intro p
      exact inverse_spin_variance_pow_le_exp (spinMean_mem_Ioo beta D v _) k
    _ ≤ _ := integral_exp_abs_field_le hbeta μ D v t (by positivity)

theorem condExp_eq_spinMean {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) (t : ℝ≥0) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => spinSign (p.1 v) | MeasurableSpace.comap (finiteObservation D t) inferInstance]
      =ᵐ[μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
        fun p => spinMean beta D v (observation t p) :=
  hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))

end Problem367.FinitePosteriorVariance

end

end OAI
