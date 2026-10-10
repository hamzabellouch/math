import OAI.Probability.InvariantIsing.Cavity.CavityProjectedSpinNumerator
import OAI.Probability.InvariantIsing.Cavity.CavityRestrictedSpinTest

namespace OAI

/-! The hard-restricted marked spin moment is the actual Gibbs
numerator with the same restriction on every replica. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma cavity_projected_restricted_spin_numerator {m r q d k : ℕ} {N : Fin m → ℕ}
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (B : (Fin r → X) → SpectralBlock m r)
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ Bcut : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator (ν.prod π)
      (fun x => if 1+‖cavitySelectedSiteProjection e v A x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C
          (cavitySelectedSiteProjection e v A x.1) x.2) τ) else 0)
      (cavityProjectedSpinTest B F) =
    ∫ σ : Fin r → X, cavityRestrictedSpinReplicaValue K L C τ Bcut
      (cavitySelectedGroupProjection e) π F
      (B σ, cavityGroupMatrixProjection (fun a i => v a (σ i)) A)
      ∂Measure.pi (fun _ => ν) := by
  let V := fun ξ : Fin r → X × Spin k =>
    (∏ i, if 1+‖cavitySelectedSiteProjection e v A (ξ i).1‖^2 ≤ 1+Bcut^2 then
      Real.exp (min (cavityLogFactor K L C
        (cavitySelectedSiteProjection e v A (ξ i).1) (ξ i).2) τ) else 0) *
      cavityProjectedSpinTest B F ξ
  have hw (x : X × Spin k) :
      (if 1+‖cavitySelectedSiteProjection e v A x.1‖^2 ≤ 1+Bcut^2 then
        Real.exp (min (cavityLogFactor K L C (cavitySelectedSiteProjection e v A x.1) x.2) τ)
        else 0) ∈ Set.Icc 0 (Real.exp τ) := by
    split_ifs
    · exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.mpr (min_le_right _ _)⟩
    · exact ⟨le_rfl,(Real.exp_pos _).le⟩
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V,cavityProjectedSpinTest]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hw (ξ i)).1))]
    exact (Finset.prod_le_prod₀ (fun i _ => (hw (ξ i)).1)
      (fun i _ => (hw (ξ i)).2)).trans_eq (by simp)
  change (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin r => ν.prod π)) = _
  rw [cavity_replica_product_integral ν π V (measurable_of_countable V) hb]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    simp only [cavityRestrictedSpinReplicaValue, cavitySelectedSiteProjection_replica]
    rfl

end InvariantIsing

end

end OAI
