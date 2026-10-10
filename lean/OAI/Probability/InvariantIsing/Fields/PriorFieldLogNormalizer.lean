import OAI.Probability.InvariantIsing.Fields.FieldLogNormalizer
import OAI.Probability.InvariantIsing.Cavity.CavityRootIntegration

namespace OAI

/-! Logarithmic field normalizers for a deterministic finite spin prior,
with joint root/forest integrability proved from the actual recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma prior_field_energy_recursion (N n : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (z : Fin N → ℝ) :
    energyRecursion n b (fun i => fieldEnergyMarkLaw N (v i))
      π (fieldEnergy z) =
    cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
      (fun _ p => p.1 + p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z := by
  induction n generalizing b v z with
  | zero => rfl
  | succ n ih =>
    let bs := fun i => b (i + 1)
    let vs := fun i => v (i + 1)
    let G := energyRecursion n bs (fun i => fieldEnergyMarkLaw N (vs i))
      π
    have hmG : Measurable G := measurable_energyRecursion _ _ _ _
    change Real.log (∫ a, Real.exp (b 0 * G (fieldEnergy z + a))
        ∂(fieldEnergyMarkLaw N (v 0) : Measure (Spin N → ℝ))) / b 0 =
      Real.log (∫ a, Real.exp (b 0 * cascadeRecursion n bs
        (fun i => vectorGaussianLaw N (vs i)) (fun _ p => p.1 + p.2)
        (fun y => finiteLogIntegral π (fieldEnergy y)) (z + a))
        ∂(vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ))) / b 0
    congr 2
    have hm : Measurable (fun a : Spin N → ℝ =>
        Real.exp (b 0 * G (fieldEnergy z + a))) :=
      ((hmG.comp (measurable_const.add measurable_id)).const_mul (b 0)).exp
    rw [show (fieldEnergyMarkLaw N (v 0) : Measure (Spin N → ℝ)) =
      (vectorGaussianLaw N (v 0) : Measure (Fin N → ℝ)).map (fieldEnergy (N := N)) from rfl,
      integral_map (measurable_fieldEnergy_map N).aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    refine ae_of_all _ fun a => ?_
    have hadd : fieldEnergy (z + a) = fieldEnergy z + fieldEnergy a := by
      ext σ
      simp only [fieldEnergy, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    dsimp only
    rw [← hadd]
    exact congrArg (fun x => Real.exp (b 0 * x)) (ih bs vs (z + a))

def priorFieldVectorLogNormalizer (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (h : FieldStep) (z : Fin N → ℝ)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) : ℝ :=
  Real.log (∫ s : Spin N × LabeledLeaf h.depth,
    Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1)
      ∂(π.prod (labeledLeafLaw h.depth p.1)))

lemma measurable_priorFieldVectorLogNormalizer (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (h : FieldStep) :
    Measurable (fun p : (Fin N → ℝ) ×
      (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        priorFieldVectorLogNormalizer N π h p.1 p.2) := by
  have hm := (measurable_labeledEnergyLog h.depth
    π).comp
      (show Measurable (fun p : (Fin N → ℝ) ×
        (LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) =>
        (fieldEnergy p.1, (p.2.1, markForestOfCoords (Spin N → ℝ) h.depth
          (fieldEnergyCoordinates N h p.2).2))) from by
            have hf := measurable_fieldEnergy_map N
            have hc := measurable_fieldEnergyCoordinates N h
            fun_prop)
  simp only [Function.comp_def, labeledEnergyLog, fieldEnergyCoordinates] at hm
  simp_rw [field_labeled_energy] at hm
  exact hm

theorem prior_field_vector_log_conditional (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (hN : 0 < N) (h : FieldStep)
    (z : Fin N → ℝ) :
    let b := chainExponent h.cut
    let μ := fun i => fieldEnergyMarkLaw N (fieldStepVariance h i)
    let X := energyRecursion h.depth b μ π (fieldEnergy z)
    Integrable (priorFieldVectorLogNormalizer N π h z) (fieldVectorCoordinateLaw N h) ∧
      (∫ p, priorFieldVectorLogNormalizer N π h z p ∂fieldVectorCoordinateLaw N h) = X ∧
      Integrable (fun p => (priorFieldVectorLogNormalizer N π h z p - X)^2)
        (fieldVectorCoordinateLaw N h) ∧
      (∫ p, (priorFieldVectorLogNormalizer N π h z p - X)^2 ∂fieldVectorCoordinateLaw N h) ≤
        4 * ∫ T, (Real.log (rawTreeTotal h.depth T).toReal)^2
          ∂(rawCascadeLaw h.depth b : Measure (RawTree h.depth)) := by
  intro b μ X
  let ν : Measure (Spin N) := π
  have hb : CascadeExponents h.depth b := chainExponent_admissible h.ordered_cut h.first h.last
  have hμ : ∀ i < h.depth, ExponentialNormMoments (μ i : Measure (Spin N → ℝ)) :=
    fun i _ => fieldEnergyMarkLaw_moments N hN (fieldStepVariance h i)
  let T := fun p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ) =>
    labeledNoiseJoin (Spin N → ℝ) h.depth
      ((fieldEnergyCoordinates N h p).1,
        markForestOfCoords (Spin N → ℝ) h.depth (fieldEnergyCoordinates N h p).2)
  have hp : MeasurePreserving T (fieldVectorCoordinateLaw N h)
      (noiseCascadeLaw (Spin N → ℝ) h.depth b μ : Measure _) :=
    (show MeasurePreserving (labeledNoiseJoin (Spin N → ℝ) h.depth)
      ((labeledCascadeLaw h.depth b : Measure (LabeledTree h.depth)).prod
        (markForestLaw (Spin N → ℝ) h.depth μ))
      (noiseCascadeLaw (Spin N → ℝ) h.depth b μ : Measure _) from
        ⟨measurable_labeledNoiseJoin _ _, labeledNoiseJoin_law _ _ _ _⟩).comp
      ((cascadeCoordinates_preserving h.depth b μ).comp (fieldEnergyCoordinates_law N h))
  have he0 := ((cascadeCoordinates_preserving h.depth b μ).comp
    (fieldEnergyCoordinates_law N h)).quasiMeasurePreserving.ae
      (labeledEnergyLog_eq_cascade h.depth b hb μ ν (fieldEnergy z))
  have he : priorFieldVectorLogNormalizer N π h z =ᵐ[fieldVectorCoordinateLaw N h]
      fun p => cascadeEnergyLog h.depth b μ ν (fieldEnergy z) (T p) := by
    filter_upwards [he0] with p hpe
    simp only [Function.comp_def, labeledEnergyLog, fieldEnergyCoordinates] at hpe
    simp_rw [field_labeled_energy] at hpe
    exact hpe
  have hc := cascadeEnergyLog_conditional h.depth b hb μ ν hμ (fieldEnergy z)
  have hs : (fun p => (priorFieldVectorLogNormalizer N π h z p - X)^2)
      =ᵐ[fieldVectorCoordinateLaw N h]
      (fun p => (cascadeEnergyLog h.depth b μ ν (fieldEnergy z) (T p) - X)^2) :=
    he.fun_comp (fun x => (x - X)^2)
  refine ⟨(hp.integrable_comp_of_integrable hc.1).congr he.symm, ?_,
    (hp.integrable_comp_of_integrable hc.2.2.1).congr hs.symm, ?_⟩
  · rw [integral_congr_ae he]
    exact (integral_comp_preserving_ae hp hc.1.aestronglyMeasurable).trans hc.2.1
  · rw [integral_congr_ae hs,
      integral_comp_preserving_ae hp hc.2.2.1.aestronglyMeasurable]
    exact hc.2.2.2

lemma prior_field_vector_root_recursion_integrable (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (hN : 0 < N) (h : FieldStep)
    (root : ℝ≥0) :
    Integrable (fun z => energyRecursion h.depth (chainExponent h.cut)
      (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
      π (fieldEnergy z))
        (vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  let G := energyRecursion h.depth (chainExponent h.cut)
    (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
    π
  have hG : Measurable G := measurable_energyRecursion _ _ _ _
  obtain ⟨C, L, _, hL, hbound⟩ := energyRecursion_linearGrowth h.depth (chainExponent h.cut)
    (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
    π
    (fun i _ => fieldEnergyMarkLaw_moments N hN (fieldStepVariance h i))
    (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
  have hi : Integrable G (fieldEnergyMarkLaw N root : Measure (Spin N → ℝ)) := by
    apply ((integrable_const C).add (((fieldEnergyMarkLaw_moments N hN root) 1).const_mul L)).mono'
      hG.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw [Real.norm_eq_abs]
    calc
      |G y| ≤ C + L * ‖y‖ := hbound y
      _ ≤ C + L * Real.exp (1 * ‖y‖) := by
        gcongr
        simpa only [one_mul] using (le_add_of_nonneg_right zero_le_one).trans
          (Real.add_one_le_exp ‖y‖)
  exact (integrable_map_measure hG.aestronglyMeasurable
    (measurable_fieldEnergy_map N).aemeasurable).mp hi

theorem prior_field_vector_log_root_integral (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (hN : 0 < N) (h : FieldStep)
    (root : ℝ≥0) :
    Integrable (fun p => priorFieldVectorLogNormalizer N π h p.1 p.2)
      ((vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) ∧
      (∫ p, priorFieldVectorLogNormalizer N π h p.1 p.2
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)).prod (fieldVectorCoordinateLaw N h)) =
      ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
        (fun i => vectorGaussianLaw N (fieldStepVariance h i))
        (fun _ p => p.1 + p.2) (fun y => finiteLogIntegral π (fieldEnergy y)) z
        ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ)) := by
  have hh := cavity_joint_integral_of_centered_square
    (vectorGaussianLaw N root : Measure (Fin N → ℝ)) (fieldVectorCoordinateLaw N h)
    (fun p => priorFieldVectorLogNormalizer N π h p.1 p.2)
    (fun z => energyRecursion h.depth (chainExponent h.cut)
      (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
      π (fieldEnergy z))
    (measurable_priorFieldVectorLogNormalizer N π h)
    ((measurable_energyRecursion _ _ _ _).comp (measurable_fieldEnergy_map N))
    (prior_field_vector_root_recursion_integrable N π hN h root)
    (fun z => (prior_field_vector_log_conditional N π hN h z).2.2.1)
    ⟨_, fun z => (prior_field_vector_log_conditional N π hN h z).2.2.2⟩
    (fun z => (prior_field_vector_log_conditional N π hN h z).2.1)
  exact ⟨hh.1, hh.2.trans (by simp_rw [prior_field_energy_recursion])⟩

theorem prior_field_vector_spin_exp_integrable (N : ℕ) (π : Measure (Spin N)) [IsProbabilityMeasure π] (hN : 0 < N) (h : FieldStep)
    (z : Fin N → ℝ) :
    ∀ᵐ p ∂fieldVectorCoordinateLaw N h,
      Integrable (fun s : Spin N × LabeledLeaf h.depth =>
        Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1))
        (π.prod (labeledLeafLaw h.depth p.1)) := by
  have he := (fieldEnergyCoordinates_law N h).quasiMeasurePreserving.ae
    (cascadeCoordinate_exp_integrable h.depth (chainExponent h.cut)
      (chainExponent_admissible h.ordered_cut h.first h.last)
      (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
      π
      (fun i _ => fieldEnergyMarkLaw_moments N hN (fieldStepVariance h i)) (fieldEnergy z))
  filter_upwards [he] with p hp
  change Integrable (fun s => Real.exp (cascadeCoordinateEnergy h.depth (fieldEnergy z)
    (fieldEnergyCoordinates N h p) s))
      (π.prod (labeledLeafLaw h.depth p.1)) at hp
  simpa only [fieldEnergyCoordinates_energy] using hp

end InvariantIsing

end

end OAI
