import OAI.Probability.InvariantIsing.Cavity.CavityResidualPartition

namespace OAI

/-! Positivity and finiteness of the actual residual-integrated normalizer. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator ENNReal

namespace InvariantIsing

lemma measurable_cavityLeafSum_joint {d : ℕ} (n : ℕ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
      cavityLeafSum n p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact ih.comp ((measurable_fst.add measurable_snd.snd.fst).prodMk
      measurable_snd.snd.snd)

lemma measurable_cavityLeafSum {d : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d)) :
    Measurable (cavityLeafSum n s) :=
  (measurable_cavityLeafSum_joint n).comp (measurable_const.prodMk measurable_id)

theorem cavity_residual_partition_pos_finite {d : ℕ} (n : ℕ)
    (K : Matrix (Fin d) (Fin d) ℝ)
    (H S : ℕ → Matrix (Fin d) (Fin d) ℝ) (b : ℕ → ℝ)
    (hbCascade : CascadeExponents n b)
    (hK : K.transpose = K) (hH : ∀ i, (H i).transpose = H i)
    (hS : ∀ i, (S i).PosSemidef) (hb : ∀ i, 0 < b i)
    (hdet : ∀ i, IsUnit (1 - H i * K).det)
    (hΔ : ∀ i, H i - H (i + 1) = b i • S i)
    (hQ : ∀ i, (cavityFactorPrecision
      (b i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef)
    (hR : (H n).PosSemidef)
    (hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) :
    ∀ᵐ V ∂(noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n b (cavityGaussianMarks S) : Measure _),
      0 < cavityResidualPartition n K (H n) s V ∧
        cavityResidualPartition n K (H n) s V < ∞ := by
  let μ := cavityGaussianMarks S
  let X := fun i z => cavityQuadraticValue n K H b i z - Real.log (1 - H n * K).det / 2
  let a := -Real.log (1 - H n * K).det / 2
  have hKh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  have hX : ∀ i, Measurable (X i) := fun i =>
    (measurable_cavityQuadraticValue n K H b i).sub_const _
  have hu : ∀ i : ℕ, Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => p.1 + p.2) :=
    fun _ => measurable_fst.add measurable_snd
  have hbase := (cavity_quadratic_cascade_log_integral n K H S b hbCascade hK hH hS hb hdet hΔ hQ s).1
  have hleaf := noiseTreeFactor_leafIntegral n b hbCascade μ hX hu s
  filter_upwards [hbase, hleaf, cavity_noiseTreeTotal_pos_finite n b hbCascade μ] with V hV he ht
  rw [← cavityResidualPartition_eq_leafIntegral n K H b hKh hR hQR s V] at he
  have hx : X = fun i z => cavityQuadraticValue n K H b i z + a := by
    funext i z
    dsimp [X, a]
    ring
  rw [hx, cavity_noiseTreeFactor_add_const] at he
  have hpos : 0 < noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V *
      cavityResidualPartition n K (H n) s V := by
    rw [← he]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos a)).ne' hV.1.ne'
  have hlt : noiseTreeTotal (EuclideanSpace ℝ (Fin d)) n V *
      cavityResidualPartition n K (H n) s V < ∞ := by
    rw [← he]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV.2
  constructor
  · by_contra h
    have hz : cavityResidualPartition n K (H n) s V = 0 :=
      le_antisymm (le_of_not_gt h) bot_le
    simp only [hz, mul_zero, lt_self_iff_false] at hpos
  · rcases ENNReal.mul_lt_top_iff.mp hlt with h | h | h
    · exact h.2
    · exact (ht.1.ne' h).elim
    · rw [h]
      exact ENNReal.zero_lt_top

/-- Finiteness of the actual residual partition entails precisely the
backward-quadratic leaf exponential integrability used by its tilted law. -/
lemma cavity_residual_partition_leaf_integrable {d : ℕ} (n : ℕ)
    (K R : Matrix (Fin d) (Fin d) ℝ) (hK : K.IsHermitian) (hR : R.PosSemidef)
    (hQ : (cavityFactorPrecision K (CFC.sqrt R)).PosDef)
    (s : EuclideanSpace ℝ (Fin d)) (V : NoiseTree (EuclideanSpace ℝ (Fin d)) n)
    (hZ : cavityResidualPartition n K R s V < ∞) :
    Integrable (fun v => Real.exp (⟪cavityLeafSum n s v,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R)
        (cavityLeafSum n s v)⟫ / 2))
      (noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) := by
  let f := fun v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n =>
    Real.exp (⟪cavityLeafSum n s v,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (cavityBackwardQuadratic K R)
        (cavityLeafSum n s v)⟫ / 2)
  let c := ENNReal.ofReal (Real.exp (-Real.log (1 - R * K).det / 2))
  have hc : 0 < c := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hm : Measurable f := by
    dsimp [f]
    have hs := measurable_cavityLeafSum n s
    fun_prop
  have he : cavityResidualPartition n K R s V =
      c * ∫⁻ v, ENNReal.ofReal (f v) ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V := by
    unfold cavityResidualPartition
    simp_rw [cavity_residual_lintegral K R hK hR hQ, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hL : (∫⁻ v, ENNReal.ofReal (f v)
      ∂noiseLeafKernel (EuclideanSpace ℝ (Fin d)) n V) < ∞ := by
    rw [he] at hZ
    rcases ENNReal.mul_lt_top_iff.mp hZ with h | h | h
    · exact h.2
    · exact (hc.ne' h).elim
    · rw [h]
      exact ENNReal.zero_lt_top
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [f, Real.enorm_eq_ofReal_abs, abs_of_pos (Real.exp_pos _)] using hL

end InvariantIsing

end

end OAI
