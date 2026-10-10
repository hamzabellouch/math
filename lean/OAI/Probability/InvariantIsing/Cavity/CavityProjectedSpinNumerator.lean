import OAI.Probability.InvariantIsing.Cavity.CavityExtraReplicaPrefix
import OAI.Probability.InvariantIsing.Cavity.CavityCappedSpinTest

namespace OAI

/-! Exact spin-prior numerators for the selected physical Haar projections.
The shared projection matrix remains outside the replica product measure. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators BoundedContinuousFunction

namespace InvariantIsing

def cavitySelectedSiteProjection {m q d : ℕ} {N : Fin m → ℕ} {X : Type*}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) (x : X) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => ∑ l, v (e j).1 x l * A (e j).1 l (e j).2)

lemma cavitySelectedSiteProjection_replica {m r q d : ℕ} {N : Fin m → ℕ} {X : Type*}
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) (σ : Fin r → X) :
    cavitySelectedGroupProjection e
      (cavityGroupMatrixProjection (fun a i => v a (σ i)) A) =
      fun i => cavitySelectedSiteProjection e v A (σ i) := by
  funext i
  ext j
  rfl

def cavityProjectedSpinTest {m r d : ℕ} {X : Type*}
    (B : (Fin r → X) → SpectralBlock m r)
    (F : SpectralBlock m r × (Fin r → Spin d) →ᵇ ℝ)
    (ξ : Fin r → X × Spin d) : ℝ :=
  F (B (fun i => (ξ i).1), fun i => (ξ i).2)

lemma cavity_projected_spin_numerator {m r q d k : ℕ} {N : Fin m → ℕ}
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (B : (Fin r → X) → SpectralBlock m r)
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator (ν.prod π)
      (fun x => Real.exp (min (cavityLogFactor K L C
        (cavitySelectedSiteProjection e v A x.1) x.2) τ))
      (cavityProjectedSpinTest B F) =
    ∫ σ : Fin r → X, cavityCappedSpinReplicaValue K L C τ
      (cavitySelectedGroupProjection e) π F
      (B σ, cavityGroupMatrixProjection (fun a i => v a (σ i)) A)
      ∂Measure.pi (fun _ => ν) := by
  let V := fun ξ : Fin r → X × Spin k =>
    (∏ i, Real.exp (min (cavityLogFactor K L C
      (cavitySelectedSiteProjection e v A (ξ i).1) (ξ i).2) τ)) *
      cavityProjectedSpinTest B F ξ
  have hb (ξ) : ‖V ξ‖ ≤ (Real.exp τ)^r * ‖F‖ := by
    dsimp only [V, cavityProjectedSpinTest]
    rw [norm_mul]
    apply mul_le_mul _ (F.norm_coe_le_norm _) (norm_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))]
    exact (Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
      (fun _ _ => Real.exp_le_exp.mpr (min_le_right _ _))).trans_eq (by simp)
  change (∫ ξ, V ξ ∂Measure.pi (fun _ : Fin r => ν.prod π)) = _
  rw [cavity_replica_product_integral ν π V (measurable_of_countable V) hb]
  apply integral_congr_ae
  exact ae_of_all _ fun σ => by
    simp only [cavityCappedSpinReplicaValue, cavitySelectedSiteProjection_replica]
    rfl

lemma cavity_projected_spin_extra_replicas {m r q d k j : ℕ} {N : Fin m → ℕ}
    {X : Type*} [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (B : X → X → SpectralEntry m)
    (e : Fin d → Fin m × Fin q) (v : (a : Fin m) → X → Fin (N a) → ℝ)
    (A : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ)
    (C : Matrix (Fin k) (Fin k) ℝ) (τ : ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π]
    (F : SpectralBlock m r × (Fin r → Spin k) →ᵇ ℝ) :
    cavityWeightNumerator (ν.prod π)
      (fun x => Real.exp (min (cavityLogFactor K L C
        (cavitySelectedSiteProjection e v A x.1) x.2) τ))
      (cavityProjectedSpinTest (fun σ i l => B (σ i) (σ l)) F) *
        (cavityWeightNormalizer (ν.prod π)
          (fun x => Real.exp (min (cavityLogFactor K L C
            (cavitySelectedSiteProjection e v A x.1) x.2) τ)))^j =
      cavityWeightNumerator (ν.prod π)
        (fun x => Real.exp (min (cavityLogFactor K L C
          (cavitySelectedSiteProjection e v A x.1) x.2) τ))
        (cavityProjectedSpinTest (fun σ i l => B (σ i) (σ l))
          (cavityReplicaPrefixTest j F)) := by
  unfold cavityWeightNumerator cavityWeightNormalizer
  rw [cavity_extra_replica_identity_fin (ν.prod π)
    (fun x => Real.exp (min (cavityLogFactor K L C
      (cavitySelectedSiteProjection e v A x.1) x.2) τ))
    (cavityProjectedSpinTest (fun σ i l => B (σ i) (σ l)) F)
    (measurable_of_countable _) (measurable_of_countable _) j]
  rfl

end InvariantIsing

end

end OAI
