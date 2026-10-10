import OAI.Probability.InvariantIsing.Cavity.CavityTiltTransport
import OAI.Probability.InvariantIsing.Cavity.CavityBaseRestrictedLaw
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteIncrement

namespace OAI

/-! Exact transport of a logarithmic cavity weight through the split
spin/leaf coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_pair_leaf_base_partition {N n depth : ℕ} (T : LabeledTree depth)
    (H : Spin N × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (x.1.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T := by
  have hp := cavity_pair_leaf_swap_preserving N n depth T
  have hi := integral_map
    (μ := ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
      (labeledLeafLaw depth T)) hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      Real.exp (H x.1))).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  have he := integral_fun_fst
    (μ := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T)
    (ν := (uniformSpinPrior n : Measure (Spin n))) (fun x => Real.exp (H x))
  rw [he] at hi
  simpa only [probReal_univ, one_smul, Function.comp_def, cavityPairLeafSwap] using hi.symm

lemma cavity_pair_leaf_full_partition {N n depth : ℕ} (T : LabeledTree depth)
    (H : Spin (N+n) × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (cavityJoinedSpin x.1,x.2))
      ∂((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T := by
  have hp := cavity_spin_pair_leaf_prior N n depth T
  have hi := integral_map
    (μ := labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
    hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      Real.exp (H (cavityJoinedSpin x.1,x.2)))).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  have he (σ : Spin (N+n)) : cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [cavityJoinedSpin, cavitySpinSplit]
  simpa only [Function.comp_def, he] using hi

lemma cavity_log_weight_map {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    [Countable X] [Countable Y] [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : MeasurePreserving f μ ν)
    (H W : Y → ℝ) :
    Real.log (∫ x, Real.exp (W (f x)) ∂μ.tilted (H ∘ f)) =
      Real.log (∫ y, Real.exp (W y) ∂ν.tilted H) := by
  have ht : (μ.tilted (H ∘ f)).map f = ν.tilted H := by
    rw [cavity_tilt_map μ f hf.measurable H (measurable_of_countable H), hf.map_eq]
  have hi := integral_map (μ := μ.tilted (H ∘ f)) hf.measurable.aemeasurable
    ((measurable_of_countable W).exp.aestronglyMeasurable)
  rw [ht] at hi
  exact congrArg Real.log hi.symm

lemma cavity_log_weight_pair_leaf {N n depth : ℕ} (T : LabeledTree depth)
    (H W : (Spin N × LabeledLeaf depth) × Spin n → ℝ) :
    Real.log (∫ x, Real.exp (W (cavityPairLeafSwap x))
      ∂(((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
        (labeledLeafLaw depth T)).tilted (H ∘ cavityPairLeafSwap)) =
    Real.log (∫ x, Real.exp (W x)
      ∂((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).prod
        (uniformSpinPrior n)).tilted H) :=
  cavity_log_weight_map _ _ _ (cavity_pair_leaf_swap_preserving N n depth T) H W

end InvariantIsing

end

end OAI
