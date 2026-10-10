import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulBundleStates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulSamplePaths

namespace OAI

/-! # Actual terminal paths for successful source bundles -/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Manifold

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E N G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N] [MeasurableSpace N]
  [MeasurableMul₂ N] [MeasurableInv N]
  [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]

theorem successful_sourceBundle_terminal_path {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin (h + 1) → N ≃* N) (sample : ℕ → ℝ → N)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin (h + 1)) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (ι : N →* G) (x d₀ : G) (A : Set N) (S : Set G)
    (d : Fin ((h + 1) * m) → ℝ → G) (hd : ∀ i, Continuous (d i))
    (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin ((h + 1) * m), Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin ((h + 1) * m), ι (sample i.val 0) = 1)
    {B κ ρ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i : Fin ((h + 1) * m), ∀ b : ℝ,
      |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) B κ ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S)
    (hinj : Function.Injective ι)
    (n : N) (hn : n ∈ A) (t : Fin ((h + 1) * m + (h + 1) * m) → ℝ)
    (ht : ‖t‖ ≤ ρ)
    (hs : SwitchSuccessful (fun _ => A) 0 ((h + 1) * m) n
      (sampledSwitchParameters sample ((h + 1) * m) t)) :
    ∃ γ : Path (x * ι n * d₀)
      (x * ι (n * prefixCoordinateEquiv (h + 1)
        (fun j => φ j (sourceBundleProduct lie Exp X s letters
          (bundleParameterChart (h + 1) m) r t j)) (Fin.last h)) * d₀),
      PathMetricBound γ (B * 2 ^ ((h + 1) * m)) (κ * 2 ^ ((h + 1) * m)) ∧
      ∀ u, γ u ∈ S := by
  obtain ⟨γ, hγ, hγS⟩ := successful_sample_path ι x d₀ A S ((h + 1) * m)
    sample hsub d hd hd₀ hf hf₀ r hB hκ hbase hstep hinj n hn t ht hs
  have he := sourceBundleState_last_eq_switchEndpoint lie Exp X s letters r φ sample
    hsub hsample n t
  exact ⟨γ.cast rfl (congrArg (fun z => x * ι z * d₀) he), hγ, hγS⟩

end PolycyclicRecognition

end

end OAI
