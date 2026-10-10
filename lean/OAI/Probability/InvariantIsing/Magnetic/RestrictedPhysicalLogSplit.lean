import OAI.Probability.InvariantIsing.Magnetic.RestrictedPhysicalGibbsSplit
import OAI.Probability.InvariantIsing.Cavity.CavityIncrementComparison

namespace OAI

/-! The literal constrained log-partition increment, including the
cavity slice's original cube mass, is its Gibbs cavity logarithm. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

theorem restricted_cavity_spin_leaf_log_increment {N n depth : ℕ}
    (S : Finset (Spin N)) (hS : S.Nonempty) (C : Finset (Spin n)) (hC : C.Nonempty)
    (T : LabeledTree depth) (J : Spin N × LabeledLeaf depth → ℝ)
    (hj : Integrable (fun x => Real.exp (J x))
      (labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T))
    (H : Spin (N+n) × LabeledLeaf depth → ℝ)
    (hH : Integrable (fun x => Real.exp (H x))
      (labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C)
        (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T))
    (V : (Spin N × LabeledLeaf depth) × Spin n → ℝ)
    (hsplit : ∀ x, H x = J (cavitySpinLeafSplit N n depth x).1 +
      V (cavitySpinLeafSplit N n depth x)) :
    (Real.log (∫ x, Real.exp (H x)
      ∂labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C)
        (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T) +
      (Real.log (cavityProductSlice S C).card - (N+n) * Real.log 2)) -
      (Real.log (∫ x, Real.exp (J x)
        ∂labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T) +
        (Real.log S.card - N * Real.log 2)) =
      Real.log (∫ x, Real.exp (V x)
        ∂((labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T).tilted J).prod
          (restrictedSpinPrior C hC)) + (Real.log C.card - n * Real.log 2) := by
  let μ := labeledSpinReference depth (restrictedSpinPrior (cavityProductSlice S C)
    (cavityProductSlice_nonempty S hS C hC) : Measure (Spin (N+n))) T
  let ν := labeledSpinReference depth (restrictedSpinPrior S hS : Measure (Spin N)) T
  let π := (restrictedSpinPrior C hC : Measure (Spin n))
  let E := fun z : (Spin N × LabeledLeaf depth) × Spin n => J z.1 + V z
  have hP := restricted_cavity_spin_leaf_split_prior S hS C hC T
  have hE : Integrable (fun z => Real.exp (E z)) (ν.prod π) := by
    rw [← hP.map_eq]
    apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable).mpr
    convert hH using 1
    funext x
    exact congrArg Real.exp (hsplit x).symm
  have he : (∫ z, Real.exp (E z) ∂ν.prod π) = ∫ x, Real.exp (H x) ∂μ := by
    have ht := hP.hasLaw.integral_comp
      (measurable_of_countable (fun z => Real.exp (E z))).aestronglyMeasurable
    calc
      _ = ∫ x, Real.exp (E (cavitySpinLeafSplit N n depth x)) ∂μ := ht.symm
      _ = _ := integral_congr_ae (ae_of_all _ fun x => congrArg Real.exp (hsplit x).symm)
  have hb : Integrable (fun z : (Spin N × LabeledLeaf depth) × Spin n => Real.exp (J z.1))
      (ν.prod π) := hj.comp_fst π
  have ht := cavity_log_tilt_factor (ν.prod π) (fun z => J z.1) V hb hE
  rw [← cavity_tilt_prod_left ν π J (measurable_of_countable _), he] at ht
  have hjmean : (∫ z : (Spin N × LabeledLeaf depth) × Spin n, Real.exp (J z.1) ∂ν.prod π) =
      ∫ x, Real.exp (J x) ∂ν := by
    rw [integral_prod _ hb]
    simp
  rw [hjmean] at ht
  rw [cavityProductSlice_log_mass S hS C hC]
  change (Real.log (∫ x, Real.exp (H x) ∂μ) + _) -
    (Real.log (∫ x, Real.exp (J x) ∂ν) + _) = _
  linarith only [ht]

end InvariantIsing

end

end OAI
