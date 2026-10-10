import OAI.Probability.InvariantIsing.Cavity.CavitySpinSplit
import OAI.Probability.InvariantIsing.Cavity.CavityContinuousReplicaTilt

namespace OAI

/-! The original spin/leaf Gibbs law equals the base Gibbs law times the
independent cavity prior, tilted by the exact cavity energy difference. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_base_product_tilt {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (J : X → ℝ) (hJ : Measurable J) (hi : Integrable (fun x => Real.exp (J x)) μ)
    (V : X × Y → ℝ) :
    ((μ.tilted J).prod ν).tilted V = (μ.prod ν).tilted (fun z => J z.1 + V z) := by
  rw [cavity_tilt_prod_left μ ν J hJ]
  have hb : Integrable (fun z : X × Y => Real.exp (J z.1)) (μ.prod ν) := hi.comp_fst ν
  exact tilted_tilted hb V

lemma cavity_base_product_tilt_integrable {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (J : X → ℝ) (hJ : Measurable J) (hi : Integrable (fun x => Real.exp (J x)) μ)
    (V : X × Y → ℝ)
    (hv : Integrable (fun z => Real.exp (J z.1 + V z)) (μ.prod ν)) :
    Integrable (fun z => Real.exp (V z)) ((μ.tilted J).prod ν) := by
  rw [cavity_tilt_prod_left μ ν J hJ]
  have hb : Integrable (fun z : X × Y => Real.exp (J z.1)) (μ.prod ν) := hi.comp_fst ν
  rw [integrable_tilted_iff hb]
  simpa only [smul_eq_mul, ← Real.exp_add] using hv

theorem cavity_spin_leaf_full_tilt {N n depth : ℕ} (T : LabeledTree depth)
    (J : Spin N × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
    (H : Spin (N+n) × LabeledLeaf depth → ℝ)
    (V : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (hsplit : ∀ x, H x = J (cavitySpinLeafSplit N n depth x).1 +
      V (cavitySpinLeafSplit N n depth x)) :
    ((labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T).tilted H).map
      (cavitySpinLeafSplit N n depth) =
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted J).prod
        (uniformSpinPrior n)).tilted V := by
  let μ := labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let E := fun z : (Spin N × LabeledLeaf depth) × Spin n => J z.1 + V z
  have hE : H = E ∘ (cavitySpinLeafSplit N n depth) := funext hsplit
  have hm := cavity_tilt_map μ (cavitySpinLeafSplit N n depth) (measurable_of_countable _)
    E (measurable_of_countable _)
  rw [← hE, (cavity_spin_leaf_split_prior N n depth T).map_eq] at hm
  refine hm.trans ?_
  change (ν.prod (uniformSpinPrior n)).tilted E =
    ((ν.tilted J).prod (uniformSpinPrior n)).tilted V
  exact (cavity_base_product_tilt ν (uniformSpinPrior n : Measure (Spin n)) J
    (measurable_of_countable _) hj V).symm

theorem cavity_spin_leaf_factor_integrable {N n depth : ℕ} (T : LabeledTree depth)
    (J : Spin N × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
    (H : Spin (N+n) × LabeledLeaf depth → ℝ)
    (hH : Integrable (fun x => Real.exp (H x))
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T))
    (V : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (hsplit : ∀ x, H x = J (cavitySpinLeafSplit N n depth x).1 +
      V (cavitySpinLeafSplit N n depth x)) :
    Integrable (fun x => Real.exp (V x))
      (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted J).prod
        (uniformSpinPrior n)) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let E := fun z : (Spin N × LabeledLeaf depth) × Spin n => J z.1 + V z
  have hi : Integrable (fun z => Real.exp (E z)) (ν.prod (uniformSpinPrior n)) := by
    rw [← (cavity_spin_leaf_split_prior N n depth T).map_eq]
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr
    convert hH using 1
    funext x
    exact congrArg Real.exp (hsplit x).symm
  change Integrable (fun x => Real.exp (V x)) ((ν.tilted J).prod (uniformSpinPrior n))
  exact cavity_base_product_tilt_integrable ν (uniformSpinPrior n : Measure (Spin n)) J
    (measurable_of_countable _) hj V hi

theorem cavity_spin_leaf_replica_split {N n depth r : ℕ} (T : LabeledTree depth)
    (J : Spin N × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T))
    (H : Spin (N+n) × LabeledLeaf depth → ℝ)
    (hH : Integrable (fun x => Real.exp (H x))
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T))
    (V : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (hsplit : ∀ x, H x = J (cavitySpinLeafSplit N n depth x).1 +
      V (cavitySpinLeafSplit N n depth x))
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    referenceReplicaMean
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T) H
      (fun σ => F (fun i => cavitySpinLeafSplit N n depth (σ i))) =
      cavityWeightedReplicaMean
        (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted J).prod
          (uniformSpinPrior n)) (fun x => Real.exp (V x)) F := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  let μ := labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T
  let := isProbabilityMeasure_tilted hj
  have he := cavity_spin_leaf_factor_integrable T J hj H hH V hsplit
  rw [referenceReplicaMean_eq_tilted μ H hH,
    cavityWeightedReplicaMean_exp _ V he]
  have hm : (μ.tilted H).map (cavitySpinLeafSplit N n depth) =
      ((ν.tilted J).prod (uniformSpinPrior n)).tilted V :=
    cavity_spin_leaf_full_tilt T J hj H V hsplit
  have hp : MeasurePreserving (fun σ : Fin r → Spin (N+n) × LabeledLeaf depth =>
      fun i => cavitySpinLeafSplit N n depth (σ i))
      (Measure.pi (fun _ : Fin r => μ.tilted H))
      (Measure.pi (fun _ : Fin r => ((ν.tilted J).prod (uniformSpinPrior n)).tilted V)) := by
    refine ⟨Measurable.of_eval (fun i => (measurable_of_countable _).comp (measurable_pi_apply i)), ?_⟩
    simpa only [hm] using Measure.pi_map_pi
      (μ := fun _ : Fin r => μ.tilted H)
      (f := fun _ : Fin r => cavitySpinLeafSplit N n depth)
      (fun _ => (measurable_of_countable _).aemeasurable)
  exact hp.hasLaw.integral_comp (measurable_of_countable F).aestronglyMeasurable

end InvariantIsing

end

end OAI
