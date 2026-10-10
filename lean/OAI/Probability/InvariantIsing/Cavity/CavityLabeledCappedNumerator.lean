import OAI.Probability.InvariantIsing.Cavity.CavityReplicaProductIntegral

namespace OAI

/-! Capped finite cavity numerators expressed using the genuine product
prior on labeled leaves, ordinary Gaussian residuals and Ising spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_labeled_capped_numerator {m n r d k : ℕ}
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (R : Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (Y : LabeledLeaf n → EuclideanSpace ℝ (Fin d))
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator ((ν.prod (multivariateGaussian 0 R)).prod π)
      (fun p => Real.exp (min (cavityLogFactor K L C (Y p.1.1 + p.1.2) p.2) τ))
      (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)) =
      ∫ z, ∫ α, cavityCappedFlatSpinValue K L C τ π (fun ε => F (B α, ε))
        (WithLp.toLp 2 (fun u => (Y (α u.1) + z u.1) u.2))
        ∂Measure.pi (fun _ : Fin r => ν)
        ∂Measure.pi (fun _ : Fin r => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) := by
  classical
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R
  let V := fun ξ : Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
    (∏ i, Real.exp (min (cavityLogFactor K L C (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) τ)) *
      F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)
  have hlog : Measurable (fun p : EuclideanSpace ℝ (Fin d) × Spin k =>
      cavityLogFactor K L C p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro ε
    exact (continuous_cavityLogFactor K L C ε).measurable
  have hlabel : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      fun i => (ξ i).1.1) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).fst.fst
  have hspin : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      fun i => (ξ i).2) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).snd
  have hw (i : Fin r) : Measurable (fun ξ :
      Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
      Real.exp (min (cavityLogFactor K L C (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) τ)) := by
    have hy : Measurable (fun ξ :
        Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        Y (ξ i).1.1 + (ξ i).1.2) := ((measurable_of_countable Y).comp
      ((measurable_pi_apply i).fst.fst)).add ((measurable_pi_apply i).fst.snd)
    exact ((hlog.comp (hy.prodMk (measurable_pi_apply i).snd)).min measurable_const).exp
  have hV : Measurable V :=
    (Finset.measurable_prod _ (fun i _ => hw i)).mul
      (F.continuous.measurable.comp (((measurable_of_countable B).comp hlabel).prodMk hspin))
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  let G := fun p : (Fin r → LabeledLeaf n) × (Fin r → EuclideanSpace ℝ (Fin d)) =>
    cavityCappedFlatSpinValue K L C τ π (fun ε => F (B p.1, ε))
      (WithLp.toLp 2 (fun u => (Y (p.1 u.1) + p.2 u.1) u.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro α
    exact (measurable_cavityCappedFlatSpinValue K L C τ π (fun ε => F (B α, ε))).comp
      (by fun_prop)
  have hGb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityCappedFlatSpinValue_bound K L C τ π _ (fun _ => F.norm_coe_le_norm _) _
  let H := fun x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d) =>
    G (fun i => (x i).1, fun i => (x i).2)
  have hH : Measurable H := hG.comp (by fun_prop)
  have heH (x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d)) :
      (∫ ε : Fin r → Spin k, V (fun i => (x i, ε i)) ∂Measure.pi (fun _ => π)) = H x := rfl
  change (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin r => (ν.prod μ).prod π)) = _
  rw [cavity_replica_product_integral (ν.prod μ) π V hV hb]
  simp_rw [heH]
  rw [cavity_replica_product_integral ν μ H hH (fun x => hGb _)]
  have hi : Integrable G ((Measure.pi (fun _ : Fin r => ν)).prod
      (Measure.pi (fun _ : Fin r => μ))) :=
    (integrable_const ((Real.exp τ)^r * ‖F‖)).mono' hG.aestronglyMeasurable
      (ae_of_all _ hGb)
  exact integral_integral_swap hi

end InvariantIsing

end

end OAI
