import OAI.Probability.InvariantIsing.Fields.FieldPublishedPairInput
import OAI.Probability.IsingPerceptron.TiltedLabelLaw

namespace OAI

/-! The actual scalar-field forest as a finite Ising energy-mark forest. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma measurable_fieldEnergy_map (N : ℕ) : Measurable (fieldEnergy (N := N)) := by
  unfold fieldEnergy
  fun_prop

lemma fieldEnergy_map_norm_le (N : ℕ) (z : Fin N → ℝ) :
    ‖fieldEnergy z‖ ≤ (N : ℝ) * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg z))).mpr
  intro σ
  change |∑ i, z i * spinValue (σ i)| ≤ _
  calc
    _ ≤ ∑ i, |z i * spinValue (σ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |z i| := by simp only [abs_mul, abs_spinValue, mul_one]
    _ ≤ ∑ _ : Fin N, ‖z‖ := Finset.sum_le_sum fun i _ => by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
    _ = _ := by simp

def fieldEnergyMarkLaw (N : ℕ) (v : ℝ≥0) : ProbabilityMeasure (Spin N → ℝ) :=
  (vectorGaussianLaw N v).map (fieldEnergy (N := N))

lemma fieldEnergyMarkLaw_moments (N : ℕ) (hN : 0 < N) (v : ℝ≥0) :
    ExponentialNormMoments (fieldEnergyMarkLaw N v : Measure (Spin N → ℝ)) := by
  intro a
  apply (integrable_map_measure (by fun_prop) (measurable_fieldEnergy_map N).aemeasurable).mpr
  have hi := vectorGaussianLaw_moments hN v (|a| * N)
  apply hi.mono' (((measurable_fieldEnergy_map N).norm.const_mul a).exp.aestronglyMeasurable)
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    a * ‖fieldEnergy z‖ ≤ |a| * ‖fieldEnergy z‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |a| * ((N : ℝ) * ‖z‖) :=
      mul_le_mul_of_nonneg_left (fieldEnergy_map_norm_le N z) (abs_nonneg _)
    _ = _ := by ring

def fieldEnergyCoordinates (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ)) :
    LabeledTree h.depth × (ForestVertex h.depth → Spin N → ℝ) :=
  (p.1, fun a => fieldEnergy (p.2 a))

lemma measurable_fieldEnergyCoordinates (N : ℕ) (h : FieldStep) :
    Measurable (fieldEnergyCoordinates N h) := by
  exact measurable_fst.prodMk (Measurable.of_eval fun a =>
    (measurable_fieldEnergy_map N).comp ((measurable_pi_apply a).comp measurable_snd))

theorem fieldEnergyCoordinates_law (N : ℕ) (h : FieldStep) :
    MeasurePreserving (fieldEnergyCoordinates N h) (fieldVectorCoordinateLaw N h)
      (cascadeCoordinateLaw h.depth (chainExponent h.cut)
        (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))) := by
  have hm : MeasurePreserving
      (fun g : ForestVertex h.depth → Fin N → ℝ => fun a => fieldEnergy (g a))
      (Measure.infinitePi (fun a : ForestVertex h.depth =>
        (vectorGaussianLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
          Measure (Fin N → ℝ))))
      (Measure.infinitePi (fun a : ForestVertex h.depth =>
        (fieldEnergyMarkLaw N (fieldStepVariance h (forestVertexDepth h.depth a)) :
          Measure (Spin N → ℝ)))) := by
    refine ⟨Measurable.of_eval (fun a =>
      (measurable_fieldEnergy_map N).comp (measurable_pi_apply a)), ?_⟩
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_fieldEnergy_map N)]
    rfl
  exact (MeasurePreserving.id (labeledCascadeLaw h.depth (chainExponent h.cut) :
    Measure (LabeledTree h.depth))).prod hm

lemma fieldEnergyCoordinates_energy (N : ℕ) (h : FieldStep)
    (p : LabeledTree h.depth × (ForestVertex h.depth → Fin N → ℝ))
    (z : Fin N → ℝ) (s : Spin N × LabeledLeaf h.depth) :
    cascadeCoordinateEnergy h.depth (fieldEnergy z) (fieldEnergyCoordinates N h p) s =
      fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1 := by
  change fieldEnergy z s.1 + ∑ i : Fin h.depth, fieldEnergy (p.2 (edgeAt h.depth s.2 i)) s.1 = _
  have he : fieldVectorEndpoint N h p z s.2 =
      z + ∑ i : Fin h.depth, p.2 (edgeAt h.depth s.2 i) := by
    ext j
    simpa only [fieldVectorEndpoint, Pi.add_apply, Finset.sum_apply] using
      labeledEnergy_edge_sum h.depth p.2 s.2 z j
  rw [he]
  simp only [fieldEnergy, Pi.add_apply, Finset.sum_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem field_vector_spin_exp_integrable (N : ℕ) (hN : 0 < N) (h : FieldStep)
    (z : Fin N → ℝ) :
    ∀ᵐ p ∂fieldVectorCoordinateLaw N h,
      Integrable (fun s : Spin N × LabeledLeaf h.depth =>
        Real.exp (fieldEnergy (fieldVectorEndpoint N h p z s.2) s.1))
        ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)) := by
  have he := (fieldEnergyCoordinates_law N h).quasiMeasurePreserving.ae
    (cascadeCoordinate_exp_integrable h.depth (chainExponent h.cut)
      (chainExponent_admissible h.ordered_cut h.first h.last)
      (fun i => fieldEnergyMarkLaw N (fieldStepVariance h i))
      (uniformSpinPrior N : Measure (Spin N))
      (fun i _ => fieldEnergyMarkLaw_moments N hN (fieldStepVariance h i)) (fieldEnergy z))
  filter_upwards [he] with p hp
  change Integrable (fun s => Real.exp (cascadeCoordinateEnergy h.depth (fieldEnergy z)
    (fieldEnergyCoordinates N h p) s))
      ((uniformSpinPrior N : Measure (Spin N)).prod (labeledLeafLaw h.depth p.1)) at hp
  simpa only [fieldEnergyCoordinates_energy] using hp

end InvariantIsing

end

end OAI
