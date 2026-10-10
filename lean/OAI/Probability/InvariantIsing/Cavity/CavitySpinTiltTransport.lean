import OAI.Probability.InvariantIsing.Cavity.CavityFullTilt
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticOneReplica

namespace OAI

/-! The remaining finite Ising tilt commutes with the actual quadratic
innovation change of variables, including the ordinary residual. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

def cavityLinearResidualPotential {d k : ℕ} (n : ℕ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin d))
    (p : (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k) : ℝ :=
  cavityLogFactor 0 L C (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2

lemma measurable_cavityLinearResidualPotential {d k : ℕ} (n : ℕ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (s : EuclideanSpace ℝ (Fin d)) : Measurable (cavityLinearResidualPotential n L C s) := by
  let E := (NoiseLeaf (EuclideanSpace ℝ (Fin d)) n × EuclideanSpace ℝ (Fin d)) × Spin k
  have hs : Measurable (fun p : E =>
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d))) :=
    ((measurable_cavityLeafSum n s).comp (measurable_fst.comp measurable_fst)).add
      (measurable_snd.comp measurable_fst)
  have hy (i : Fin d) : Measurable (fun p : E =>
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).measurable.comp hs
  have he (i : Fin k) : Measurable (fun p : E => spinValue (p.2 i)) :=
    (measurable_of_countable (spinValue : Bool → ℝ)).comp
      ((measurable_pi_apply i).comp measurable_snd)
  have hL : Measurable (fun p : E => ∑ i, ∑ j,
      (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) i * L i j *
        spinValue (p.2 j)) :=
    Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((hy i).mul_const (L i j)).mul (he j)))
  have hC : Measurable (fun p : E => cavityQuadratic C (fun i => spinValue (p.2 i))) :=
    (Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _
      (fun j _ => ((he i).mul_const (C i j)).mul (he j)))).const_mul (1 / 2)
  change Measurable (fun p : E => cavityLogFactor 0 L C
    (cavityLeafSum n s p.1.1 + p.1.2 : EuclideanSpace ℝ (Fin d)) p.2)
  convert hL.add hC using 1
  ext p
  simp [cavityLogFactor, cavityQuadratic]

theorem cavity_spin_tilt_innovation_transport {d k : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ) (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hK : K.transpose = K) (hR : (H n).PosSemidef)
    (hdet : IsUnit (1 - H n * K).det)
    (hQ : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K (H n) s V < ∞)
    (hV : NoiseGibbsRegular n b (cavityGaussianMarks S)
      (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
      (fun _ p => p.1 + p.2) s V)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] :
    (((cavityQuadraticResidualGibbs n K (H n) s V).prod π).tilted
      (cavityLinearResidualPotential n L C s)).map
        (Prod.map (cavityResidualInnovationMap n K H b s) id) =
      (((noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n
        (cavityInnovationTree n b (cavityGaussianMarks S)
          (fun i => cavityQuadraticStepWeight K (H i) (H (i + 1)) (b i))
          (fun i => cavityStepInnovation K (H i) (H (i + 1))) s V)).prod
            (multivariateGaussian 0 (cavityResolvent K (H n)))).prod π).tilted
        (cavityLinearResidualPotential n L C
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s)) := by
  let T := Prod.map (cavityResidualInnovationMap n K H b s) (id : Spin k → Spin k)
  let s' := Matrix.toEuclideanCLM (𝕜 := ℝ) (1 - H 0 * K)⁻¹ s
  have hT : Measurable T := (measurable_cavityResidualInnovationMap n K H b s).prodMap measurable_id
  have hfun : cavityLinearResidualPotential n L C s =
      cavityLinearResidualPotential n L C s' ∘ T := by
    funext p
    dsimp only [cavityLinearResidualPotential, Function.comp_def, T, Prod.map, id_eq, s']
    rw [cavity_residual_innovation_sum]
  rw [hfun, cavity_tilt_map _ T hT _ (measurable_cavityLinearResidualPotential n L C s')]
  rw [show T = Prod.map (cavityResidualInnovationMap n K H b s) id from rfl,
    ← Measure.map_prod_map _ _ (measurable_cavityResidualInnovationMap n K H b s) measurable_id,
    Measure.map_id]
  have he := cavity_residual_innovation_leaf_law n K H S b hK hR hdet hQ s V hZ hV
  change (cavityQuadraticResidualGibbs n K (H n) s V).map
    (cavityResidualInnovationMap n K H b s) = _ at he
  rw [he]

end InvariantIsing

end

end OAI
