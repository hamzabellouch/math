import OAI.Probability.MatroidSecretary.Weights.FiniteWeightLawModel

namespace OAI

/-!
Finite conditional-kernel bridge for the secretary transport.  The algebraic
fiber identity is a hypothesis of these reusable lemmas, not a substitute for
proving that identity for the manuscript's actual source-seed law.
-/

namespace MatroidProphet.FiniteLaw

open MeasureTheory
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

@[simp] theorem weightPMF_apply (p : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (a : α) :
    weightPMF p hp hp1 a = ENNReal.ofReal (p a) := rfl

instance weightMeasure_probability [MeasurableSpace α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    IsProbabilityMeasure (weightMeasure p hp hp1) := by
  unfold weightMeasure
  infer_instance

theorem weightMeasure_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (a : α) :
    weightMeasure p hp hp1 {a} = ENNReal.ofReal (p a) := by
  exact PMF.toMeasure_apply_singleton _ a (MeasurableSet.singleton a)

theorem integral_weightMeasure [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (f : α → ℝ) :
    (∫ a, f a ∂weightMeasure p hp hp1) = ∑ a, p a * f a := by
  rw [weightMeasure, PMF.integral_eq_sum]
  simp only [weightPMF_apply, ENNReal.toReal_ofReal (hp _), smul_eq_mul]

theorem sum_real_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    (∑ a, μ.real {a}) = 1 := by
  simp

/-- No finite-law assumption is added: every probability measure on a finite
discrete space is exactly the measure of its real singleton weights. -/
theorem weightMeasure_real_singleton [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    weightMeasure (fun a => μ.real {a}) (fun _ => measureReal_nonneg)
      (sum_real_singleton μ) = μ := by
  apply Measure.ext_of_singleton
  intro a
  rw [weightMeasure_singleton, measureReal_def]
  exact ENNReal.ofReal_toReal (measure_ne_top μ {a})

omit [Fintype β] in
theorem map_real_singleton
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (obs : α → β) (b : β) :
    (μ.map obs).real {b} = ∑ a, if obs a = b then μ.real {a} else 0 := by
  classical
  have hs : ((Finset.univ.filter fun a => obs a = b : Finset α) : Set α) =
      obs ⁻¹' {b} := by
    ext a
    simp
  rw [← Finset.sum_filter, sum_measureReal_singleton, hs]
  simp only [measureReal_def,
    Measure.map_apply (measurable_of_countable obs) (MeasurableSet.singleton b)]

@[simp] theorem kernelJointPMF_apply
    (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (b : β) (a : α) :
    kernelJointPMF m k hm hm1 hk hk1 (b, a) = ENNReal.ofReal (m b * k b a) := rfl

instance kernelJointMeasure_probability [MeasurableSpace α] [MeasurableSpace β]
    (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1) :
    IsProbabilityMeasure (kernelJointMeasure m k hm hm1 hk hk1) := by
  unfold kernelJointMeasure
  infer_instance

theorem integral_kernelJointMeasure
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (f : β × α → ℝ) :
    (∫ ba, f ba ∂kernelJointMeasure m k hm hm1 hk hk1) =
      ∫ b, ∫ a, f (b, a) ∂weightMeasure (k b) (hk b) (hk1 b)
        ∂weightMeasure m hm hm1 := by
  rw [kernelJointMeasure, kernelJointPMF]
  change (∫ ba, f ba ∂weightMeasure _ _ _) = _
  rw [integral_weightMeasure, Fintype.sum_prod_type, integral_weightMeasure]
  simp_rw [integral_weightMeasure, Finset.mul_sum, mul_assoc]

theorem kernelJointPMF_eq_map
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (obs : α → β) (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (hjoint : ∀ b a, m b * k b a = if obs a = b then p a else 0) :
    kernelJointPMF m k hm hm1 hk hk1 =
      (weightPMF p hp hp1).map (fun a => (obs a, a)) := by
  classical
  ext ba : 1
  obtain ⟨b, a⟩ := ba
  rw [kernelJointPMF_apply, hjoint]
  simp only [PMF.map_apply, tsum_fintype, Prod.mk.injEq, weightPMF_apply]
  rw [Finset.sum_eq_single a]
  · by_cases h : obs a = b
    · simp [h]
    · have h' : b ≠ obs a := Ne.symm h
      simp [h, h']
  · intro a' _ hne
    simp [Ne.symm hne]
  · simp

theorem kernelJointMeasure_eq_map
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (obs : α → β) (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (hjoint : ∀ b a, m b * k b a = if obs a = b then p a else 0) :
    kernelJointMeasure m k hm hm1 hk hk1 =
      (weightMeasure p hp hp1).map (fun a => (obs a, a)) := by
  rw [kernelJointMeasure, kernelJointPMF_eq_map p hp hp1 obs m k hm hm1 hk hk1 hjoint]
  exact (PMF.toMeasure_map (fun a => (obs a, a)) (weightPMF p hp hp1)
    (measurable_of_countable _)).symm

/-- The joint law transports every statistic of the observation and full seed,
not merely statistics of the sacrificed mask. -/
theorem integral_reconstruction
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (obs : α → β) (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (hjoint : ∀ b a, m b * k b a = if obs a = b then p a else 0)
    (f : β × α → ℝ) :
    (∫ b, ∫ a, f (b, a) ∂weightMeasure (k b) (hk b) (hk1 b)
        ∂weightMeasure m hm hm1) =
      ∫ a, f (obs a, a) ∂weightMeasure p hp hp1 := by
  rw [← integral_kernelJointMeasure m k hm hm1 hk hk1 f,
    kernelJointMeasure_eq_map p hp hp1 obs m k hm hm1 hk hk1 hjoint]
  exact integral_map_of_stronglyMeasurable (measurable_of_countable _)
    (measurable_of_countable f).stronglyMeasurable

/-- Every positive-mass reconstructed joint outcome has exactly its advertised
observation. Zero-mass fibers are not silently ruled out. -/
theorem observation_eq_of_joint_support
    (p : α → ℝ) (obs : α → β) (m : β → ℝ) (k : β → α → ℝ)
    (hm : ∀ b, 0 ≤ m b) (hm1 : ∑ b, m b = 1)
    (hk : ∀ b a, 0 ≤ k b a) (hk1 : ∀ b, ∑ a, k b a = 1)
    (hjoint : ∀ b a, m b * k b a = if obs a = b then p a else 0)
    (b : β) (a : α)
    (ha : (b, a) ∈ (kernelJointPMF m k hm hm1 hk hk1).support) : obs a = b := by
  rw [PMF.mem_support_iff, kernelJointPMF_apply, hjoint] at ha
  by_contra h
  exact ha (by simp [h])

end MatroidProphet.FiniteLaw

end OAI
