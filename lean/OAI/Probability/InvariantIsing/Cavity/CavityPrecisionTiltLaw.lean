import OAI.Probability.InvariantIsing.Cavity.CavityPrecisionTiltMoments
import Mathlib.Probability.Moments.ComplexMGF

namespace OAI

/-! Identification of the full Gaussian law under a quadratic tilt.
The proof uses the already computed Laplace transforms, so it does not
require a density with respect to Lebesgue measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

private lemma cavity_charFun_projection {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (v : EuclideanSpace ℝ (Fin d)) :
    charFun μ v = charFun (μ.map (fun z => ⟪v, z⟫)) 1 := by
  have he : (fun z : EuclideanSpace ℝ (Fin d) => ⟪z, v⟫) = (fun z => ⟪v, z⟫) :=
    funext fun z => real_inner_comm _ _
  have h := charFun_map_eq_charFun_map_inner_one (μ := μ) (Y := id) aemeasurable_id v
  simpa only [Measure.map_id, id_eq, he] using h

private lemma cavity_law_eq_of_projection_mgf {d : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hmgf : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ),
      mgf (fun z => ⟪v, z⟫) μ t = mgf (fun z => ⟪v, z⟫) ν t)
    (hpos : ∀ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), 0 < mgf (fun z => ⟪v, z⟫) μ t) :
    μ = ν := by
  apply Measure.ext_of_charFun
  funext v
  let X : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ⟪v, z⟫
  have hm : mgf X μ = mgf X ν := funext (hmgf v)
  have hd : integrableExpSet X μ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    change Integrable (fun z => Real.exp (t * X z)) μ
    exact mgf_pos_iff.mp (hpos v t)
  have hc := eqOn_complexMGF_of_mgf hm
    (show Complex.I ∈ {z : ℂ | z.re ∈ interior (integrableExpSet X μ)} from
      by simp only [Set.mem_ofPred_eq, hd, interior_univ, Set.mem_univ])
  rw [cavity_charFun_projection μ v, cavity_charFun_projection ν v]
  rw [← complexMGF_mul_I (μ := μ) (X := X) (by fun_prop) 1,
    ← complexMGF_mul_I (μ := ν) (X := X) (by fun_prop) 1]
  simpa only [Complex.ofReal_one, one_mul] using hc

/-- The normalized quadratic tilt of a standard Gaussian has the full
Gaussian law with mean `Q⁻¹l` and covariance `Q⁻¹`. -/
theorem cavity_precision_tilt_law {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef) (l : EuclideanSpace ℝ (Fin d)) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).tilted (cavityPrecisionPotential Q l) =
      multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) Q⁻¹ l) Q⁻¹ := by
  have := isProbabilityMeasure_tilted (cavity_precision_potential_integrable Q hQ l)
  apply cavity_law_eq_of_projection_mgf
  · intro v t
    rw [cavity_precision_tilt_mgf Q hQ, cavity_multivariate_gaussian_mgf Q⁻¹ hQ.inv.posSemidef]
  · intro v t
    rw [cavity_precision_tilt_mgf Q hQ]
    exact Real.exp_pos _

end InvariantIsing

end

end OAI
