import OAI.Probability.InvariantIsing.Cavity.CavityProjectedForest
import OAI.Probability.InvariantIsing.Cavity.CavitySpinFullLaw
import OAI.Probability.InvariantIsing.Cavity.CavityResidualSpinLaw

namespace OAI

/-! Projection of the actual linear cavity spin tilt to its scalar fields. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators Matrix NNReal

namespace InvariantIsing

lemma cavity_linear_factor_project {d k : ℕ}
    (L : Matrix (Fin d) (Fin k) ℝ) (c : ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin k) :
    cavityLogFactor 0 L (c • 1) y ε =
      fieldEnergy (cavityProjectField L y) ε + (k : ℝ) * c / 2 := by
  have hcross : (∑ i, ∑ j, y i * L i j * spinValue (ε j)) =
      fieldEnergy (cavityProjectField L y) ε := by
    rw [Finset.sum_comm]
    change (∑ j, ∑ i, y i * L i j * spinValue (ε j)) =
      ∑ j, (L.transpose *ᵥ fun i => y i) j * spinValue (ε j)
    simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc : cavityQuadratic (c • (1 : Matrix (Fin k) (Fin k) ℝ))
      (fun j => spinValue (ε j)) = (k : ℝ) * c / 2 := by
    have hs (i : Fin k) : spinValue (ε i) * c * spinValue (ε i) = c := by
      rw [mul_right_comm, ← pow_two, spinValue_sq, one_mul]
    simp [cavityQuadratic, Matrix.one_apply, mul_ite, ite_mul, hs]
    ring
  simp only [cavityLogFactor, hcross, hc]
  have hz : cavityQuadratic (0 : Matrix (Fin d) (Fin d) ℝ) y = 0 := by
    simp [cavityQuadratic]
  rw [hz, zero_add]

def cavityResidualFieldProjection {A : Type*} {d k : ℕ}
    (L : Matrix (Fin d) (Fin k) ℝ)
    (p : (A × EuclideanSpace ℝ (Fin d)) × Spin k) :
    (A × (Fin k → ℝ)) × Spin k := ((p.1.1, cavityProjectField L p.1.2), p.2)

lemma measurable_cavityResidualFieldProjection {A : Type*} [MeasurableSpace A] {d k : ℕ}
    (L : Matrix (Fin d) (Fin k) ℝ) :
    Measurable (cavityResidualFieldProjection (A := A) L) :=
  (measurable_fst.fst.prodMk ((measurable_cavityProjectField L).comp
    measurable_fst.snd)).prodMk measurable_snd

theorem cavity_projected_linear_spin_law {A : Type*} [MeasurableSpace A]
    {d k : ℕ} (ν : Measure A) [IsProbabilityMeasure ν]
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (L : Matrix (Fin d) (Fin k) ℝ) (v : ℝ≥0)
    (hcov : L.transpose * S * L = (v : ℝ) • 1)
    (y : A → EuclideanSpace ℝ (Fin d)) (hy : Measurable y)
    (c : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    ((((ν.prod (multivariateGaussian 0 S)).prod π).tilted
      (fun p => cavityLogFactor 0 L (c • 1)
        (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)).map
          (cavityResidualFieldProjection L)) =
      ((ν.prod (vectorGaussianLaw k v)).prod π).tilted
        (fun p => fieldEnergy (cavityProjectField L (y p.1.1) + p.1.2) p.2 +
          (k : ℝ) * c / 2) := by
  let F := cavityResidualFieldProjection (A := A) L
  let f : (A × (Fin k → ℝ)) × Spin k → ℝ := fun p =>
    fieldEnergy (cavityProjectField L (y p.1.1) + p.1.2) p.2 + (k : ℝ) * c / 2
  have hF : Measurable F := measurable_cavityResidualFieldProjection L
  have hf : Measurable f := by
    have hfield : Measurable (fun p : (A × (Fin k → ℝ)) × Spin k =>
        cavityProjectField L (y p.1.1)) :=
      (measurable_cavityProjectField L).comp (hy.comp measurable_fst.fst)
    unfold f fieldEnergy
    fun_prop
  have he : (fun p : (A × EuclideanSpace ℝ (Fin d)) × Spin k =>
      cavityLogFactor 0 L (c • 1) (y p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2) =
        f ∘ F := by
    funext p
    rw [cavity_linear_factor_project, cavityProjectField_add]
    rfl
  have hG := (cavity_scalar_projected_field_law S hS L v hcov).map_eq
  have hp : (ν.prod (multivariateGaussian 0 S)).map
      (Prod.map id (cavityProjectField L)) = ν.prod (vectorGaussianLaw k v) := by
    rw [← Measure.map_prod_map ν (multivariateGaussian 0 S) measurable_id
      (measurable_cavityProjectField L), Measure.map_id]
    exact congrArg (Measure.prod ν) hG
  have hpp : (((ν.prod (multivariateGaussian 0 S)).prod π).map F) =
      (ν.prod (vectorGaussianLaw k v)).prod π := by
    change (((ν.prod (multivariateGaussian 0 S)).prod π).map
      (Prod.map (Prod.map id (cavityProjectField L)) id)) = _
    rw [← Measure.map_prod_map _ π (measurable_id.prodMap
      (measurable_cavityProjectField L)) measurable_id, hp, Measure.map_id]
  rw [he, cavity_tilt_map _ F hF f hf, hpp]

end InvariantIsing

end

end OAI
