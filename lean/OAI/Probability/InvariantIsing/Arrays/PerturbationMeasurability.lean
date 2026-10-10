import OAI.Probability.InvariantIsing.Arrays.PerturbationFeatures

namespace OAI

/-! Jointly measurable Haar-dependent Gaussian tensor fields. -/

noncomputable section

open MeasureTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cylinderField_add (a b : ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (a + b) g = cylinderField a g + cylinderField b g :=
  Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

lemma cylinderField_single (j : ℕ) (c : ℝ) (g : ℕ → ℝ) :
    cylinderField (Finsupp.single j c) g = c * g j :=
  Finsupp.sum_single_index (zero_mul _)

lemma cylinderField_finset_sum {ι : Type*} (s : Finset ι) (a : ι → ℕ →₀ ℝ) (g : ℕ → ℝ) :
    cylinderField (∑ i ∈ s, a i) g = ∑ i ∈ s, cylinderField (a i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cylinderField]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, cylinderField_add, ih]

lemma cylinderField_featureCoefficients {J : Type*} [Fintype J]
    (tag : J → ℕ) (c : J → ℝ) (g : ℕ → ℝ) :
    cylinderField (featureCoefficients tag c) g = ∑ j, c j * g (tag j) := by
  rw [featureCoefficients, cylinderField_finset_sum]
  simp_rw [cylinderField_single]

lemma measurable_jointSpectralMonomialField {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ)
    (x : Spin N × LabeledLeaf n) :
    Measurable (fun p : SpecialOrthogonal N × (ℕ → ℝ) =>
      cylinderField (jointSpectralMonomialCoefficients (specialRotation p.1) I d n r x) p.2) := by
  unfold jointSpectralMonomialCoefficients treeFieldCoefficients
  simp_rw [cylinderField_featureCoefficients]
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_spectralMonomialFeature I d x.1 j.2).comp measurable_fst |>.const_mul _).mul
    ((measurable_pi_apply _).comp measurable_snd)

/-- This is the joint field measurability required for conditioning Gaussian
integration by parts on the random Haar rotation. -/
theorem measurable_jointSpectralMonomialFields {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : (SpecialOrthogonal N × (ℕ → ℝ)) × (Spin N × LabeledLeaf n) =>
      cylinderField (jointSpectralMonomialCoefficients (specialRotation p.1.1) I d n r p.2) p.1.2) := by
  exact measurable_from_prod_countable_left (measurable_jointSpectralMonomialField I d n r)

lemma measurable_projectedOverlap {N : ℕ} (I : Finset (Fin N)) (σ τ : Spin N) :
    Measurable (fun U : SpecialOrthogonal N => projectedOverlap (specialRotation U) I σ τ) := by
  unfold projectedOverlap
  exact (Finset.measurable_sum I (fun i _ =>
    (measurable_specialRotation_eval (spinVector σ) i).mul
      (measurable_specialRotation_eval (spinVector τ) i))).const_mul _

theorem measurable_jointSpectralMonomialCovariance {N m : ℕ}
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ) (n r : ℕ) :
    Measurable (fun p : SpecialOrthogonal N ×
        ((Spin N × LabeledLeaf n) × (Spin N × LabeledLeaf n)) =>
      cylinderCross (jointSpectralMonomialCoefficients (specialRotation p.1) I d n r p.2.1)
        (jointSpectralMonomialCoefficients (specialRotation p.1) I d n r p.2.2)) := by
  apply measurable_from_prod_countable_left
  intro xy
  simp only [jointSpectralMonomialCoefficients_cross]
  exact (Finset.measurable_prod Finset.univ (fun a _ =>
    (measurable_projectedOverlap (I a) xy.1.1 xy.2.1).pow_const (d a))).mul_const _

end InvariantIsing

end

end OAI
