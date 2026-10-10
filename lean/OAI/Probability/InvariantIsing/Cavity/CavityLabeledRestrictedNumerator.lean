import OAI.Probability.InvariantIsing.Cavity.CavityReplicaProductIntegral
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedFactor

namespace OAI

/-! Hard-restricted finite cavity numerators expressed using the genuine product
prior on labeled leaves, ordinary Gaussian residuals and Ising spins. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped Matrix BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_labeled_restricted_numerator {m n r d k : ℕ}
    (ν : Measure (LabeledLeaf n)) [IsProbabilityMeasure ν]
    (R : Matrix (Fin d) (Fin d) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ) (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (Y : LabeledLeaf n → EuclideanSpace ℝ (Fin d))
    (B : (Fin r → LabeledLeaf n) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator ((ν.prod (multivariateGaussian 0 R)).prod π)
      (fun p => cavityRestrictedFactor K L C τ Bcut (Y p.1.1 + p.1.2) p.2)
      (fun ξ => F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)) =
      ∫ z, ∫ α, cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))
        (WithLp.toLp 2 (fun u => (Y (α u.1) + z u.1) u.2))
        ∂Measure.pi (fun _ : Fin r => ν)
        ∂Measure.pi (fun _ : Fin r => multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R) := by
  classical
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) R
  let V := fun ξ : Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
    (∏ i, cavityRestrictedFactor K L C τ Bcut (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) *
      F (B (fun i => (ξ i).1.1), fun i => (ξ i).2)
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
      cavityRestrictedFactor K L C τ Bcut (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2) := by
    have hy : Measurable (fun ξ :
        Fin r → (LabeledLeaf n × EuclideanSpace ℝ (Fin d)) × Spin k =>
        Y (ξ i).1.1 + (ξ i).1.2) := ((measurable_of_countable Y).comp
      ((measurable_pi_apply i).fst.fst)).add ((measurable_pi_apply i).fst.snd)
    exact measurable_cavityRestrictedFactor_comp K L C τ Bcut _ hy _ (measurable_pi_apply i).snd
  have hV : Measurable V :=
    (Finset.measurable_prod _ (fun i _ => hw i)).mul
      (F.continuous.measurable.comp (((measurable_of_countable B).comp hlabel).prodMk hspin))
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    have hwpos i := (cavityRestrictedFactor_mem K L C τ Bcut
      (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2).1
    have hwle i := (cavityRestrictedFactor_mem K L C τ Bcut
      (Y (ξ i).1.1 + (ξ i).1.2) (ξ i).2).2
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun i _ => hwpos i))]
    exact (Finset.prod_le_prod₀ (fun i _ => hwpos i) (fun i _ => hwle i)).trans_eq (by simp)
  let G := fun p : (Fin r → LabeledLeaf n) × (Fin r → EuclideanSpace ℝ (Fin d)) =>
    cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B p.1, ε))
      (WithLp.toLp 2 (fun u => (Y (p.1 u.1) + p.2 u.1) u.2))
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro α
    exact (measurable_cavityRestrictedFlatSpinValue K L C τ Bcut π (fun ε => F (B α, ε))).comp
      (by fun_prop)
  have hGb (p) : ‖G p‖ ≤ (Real.exp τ)^r * ‖F‖ :=
    cavityRestrictedFlatSpinValue_bound K L C τ Bcut π _ (fun _ => F.norm_coe_le_norm _) _
  let H := fun x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d) =>
    G (fun i => (x i).1, fun i => (x i).2)
  have hH : Measurable H := hG.comp (by fun_prop)
  have heH (x : Fin r → LabeledLeaf n × EuclideanSpace ℝ (Fin d)) :
      (∫ ε : Fin r → Spin k, V (fun i => (x i, ε i)) ∂Measure.pi (fun _ => π)) = H x := by
    simp only [H,G,cavityRestrictedFlatSpinValue_eq]
    rfl
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
