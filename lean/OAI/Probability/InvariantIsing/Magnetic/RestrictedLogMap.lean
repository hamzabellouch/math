import OAI.Probability.InvariantIsing.Magnetic.RestrictedProductPrior
import OAI.Probability.InvariantIsing.Cavity.CavityLogMap

namespace OAI

/-! Logarithmic cavity transport for the actual constrained spin priors. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma restricted_pair_leaf_swap_preserving {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (T : LabeledTree depth) :
    MeasurePreserving (cavityPairLeafSwap (N := N) (n := n) (depth := depth))
      (((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
        (labeledLeafLaw depth T))
      ((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
        (restrictedSpinPrior C hC)) := by
  have h₁ := measurePreserving_prodAssoc (restrictedSpinPrior S hS : Measure (Spin N))
    (restrictedSpinPrior C hC : Measure (Spin n)) (labeledLeafLaw depth T)
  have h₂ := (MeasurePreserving.id (restrictedSpinPrior S hS : Measure (Spin N))).prod
    (Measure.measurePreserving_swap (μ := (restrictedSpinPrior C hC : Measure (Spin n)))
      (ν := labeledLeafLaw depth T))
  have h₃ := (measurePreserving_prodAssoc (restrictedSpinPrior S hS : Measure (Spin N))
    (labeledLeafLaw depth T) (restrictedSpinPrior C hC : Measure (Spin n))).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

lemma restricted_pair_leaf_base_partition {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (T : LabeledTree depth)
    (H : Spin N × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (x.1.1,x.2))
      ∂((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T := by
  have hp := restricted_pair_leaf_swap_preserving S hS C hC T
  have hi := integral_map
    (μ := ((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
      (labeledLeafLaw depth T)) hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × LabeledLeaf depth) × Spin n =>
      Real.exp (H x.1))).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  have he := integral_fun_fst
    (μ := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T)
    (ν := (restrictedSpinPrior C hC : Measure (Spin n))) (fun x => Real.exp (H x))
  rw [he] at hi
  simpa only [probReal_univ, one_smul, Function.comp_def, cavityPairLeafSwap] using hi.symm

lemma restricted_pair_leaf_full_partition {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (T : LabeledTree depth)
    (H : Spin (N+n) × LabeledLeaf depth → ℝ) :
    (∫ x : (Spin N × Spin n) × LabeledLeaf depth, Real.exp (H (cavityJoinedSpin x.1,x.2))
      ∂((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
        (labeledLeafLaw depth T)) =
    ∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T := by
  have hp := (restricted_cavity_spin_split_prior S hS C hC).prod (MeasurePreserving.id (labeledLeafLaw depth T))
  have hi := integral_map
    (μ := labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C) (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T)
    hp.measurable.aemeasurable
    ((measurable_of_countable (fun x : (Spin N × Spin n) × LabeledLeaf depth =>
      Real.exp (H (cavityJoinedSpin x.1,x.2)))).aestronglyMeasurable)
  unfold labeledSpinReference at hi ⊢
  rw [hp.map_eq] at hi
  have he (σ : Spin (N+n)) : cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [cavityJoinedSpin, cavitySpinSplit]
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq, he] using hi

lemma restricted_log_weight_pair_leaf {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty) (T : LabeledTree depth)
    (H W : (Spin N × LabeledLeaf depth) × Spin n → ℝ) :
    Real.log (∫ x, Real.exp (W (cavityPairLeafSwap x))
      ∂(((restrictedSpinPrior S hS : Measure (Spin N)).prod (restrictedSpinPrior C hC)).prod
        (labeledLeafLaw depth T)).tilted (H ∘ cavityPairLeafSwap)) =
    Real.log (∫ x, Real.exp (W x)
      ∂((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).prod
        (restrictedSpinPrior C hC)).tilted H) :=
  cavity_log_weight_map _ _ _ (restricted_pair_leaf_swap_preserving S hS C hC T) H W

end InvariantIsing

end

end OAI
