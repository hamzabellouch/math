import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakSubsequence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEvaluationContinuity
import Mathlib.Topology.Sequences

namespace OAI

/-! # Bounded physical convergence determines weak convergence in Y -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousY_weak_of_physical_limit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : ℕ → HomogeneousY a k) (v : HomogeneousY a k)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hp : ∀ y : E, Tendsto (fun n => homogeneousPhysicalCLM a k ha ha1 hk (u n) y)
      atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk v y)))
    (ℓ : HomogeneousY a k →L[ℝ] ℂ) :
    Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v)) := by
  apply (isCompact_closedBall (0 : ℂ) (‖ℓ‖ * M)).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [] with n
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (ℓ.le_opNorm (u n)).trans (mul_le_mul_of_nonneg_left (hu n) (norm_nonneg ℓ))
  · intro z _ hz
    obtain ⟨σ, hσ, hσz⟩ := hz.tendsto_subseq
    obtain ⟨w, _, φ, hφ, hw⟩ := homogeneousY_weak_subsequence a k M ha1 hk
      (u ∘ σ) (fun n => hu (σ n))
    have he : w = v := by
      apply homogeneousPhysicalCLM_injective a k ha ha1 hk
      ext y
      have h₁ := hw ((homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ)
      have h₂ := (hp y).comp (hσ.comp hφ).tendsto_atTop
      exact tendsto_nhds_unique h₁ h₂
    have h₁ := hσz.comp hφ.tendsto_atTop
    have h₂ := hw ℓ
    rw [he] at h₂
    exact tendsto_nhds_unique h₁ h₂

theorem homogeneousY_exists_of_physical_limit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : ℕ → HomogeneousY a k) (w : E → ℂ)
    (hu : ∀ n, ‖u n‖ ≤ M)
    (hp : ∀ y : E, Tendsto (fun n => homogeneousPhysicalCLM a k ha ha1 hk (u n) y)
      atTop (𝓝 (w y))) :
    ∃ v : HomogeneousY a k, ‖v‖ ≤ M ∧
      (∀ y, homogeneousPhysicalCLM a k ha ha1 hk v y = w y) ∧
      ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v)) := by
  obtain ⟨v, hv, φ, hφ, hw⟩ := homogeneousY_weak_subsequence a k M ha1 hk u hu
  have he (y : E) : homogeneousPhysicalCLM a k ha ha1 hk v y = w y :=
    tendsto_nhds_unique
      (hw ((homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ))
      ((hp y).comp hφ.tendsto_atTop)
  refine ⟨v, hv, he, ?_⟩
  intro ℓ
  apply homogeneousY_weak_of_physical_limit a k M ha ha1 hk u v hu (ℓ := ℓ)
  intro y
  rw [he y]
  exact hp y

theorem continuous_functional_of_physical {X : Type*} [TopologicalSpace X]
    [SequentialSpace X] (a k M : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u : X → HomogeneousY a k) (hu : ∀ x, ‖u x‖ ≤ M)
    (hp : ∀ y : E, Continuous (fun x => homogeneousPhysicalCLM a k ha ha1 hk (u x) y))
    (ℓ : HomogeneousY a k →L[ℝ] ℂ) : Continuous (fun x => ℓ (u x)) := by
  apply continuous_iff_seqContinuous.mpr
  intro x v hv
  apply homogeneousY_weak_of_physical_limit a k M ha ha1 hk (u ∘ x) (u v)
    (fun n => hu (x n)) (ℓ := ℓ)
  intro y
  exact ((hp y).tendsto v).comp hv

end DefocusingNLS

end OAI
