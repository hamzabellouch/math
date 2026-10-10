import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulSampleBlockPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SuccessfulBundleStates

namespace OAI

/-! # Exact source-bundle boundaries and their individual paths -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N]

/-- The product of each actual sampled block is its prescribed conjugated
source-bundle product. -/
theorem sampledBlockWord_source_product {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (t : Fin (h * m + h * m) → ℝ) (i : Fin h) :
    (sampledBlockWord sample t i).prod =
      φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) := by
  simp only [sampledBlockWord, sourceBundleProduct, bundleParameterChart_left,
    bundleParameterChart_right, map_list_prod, List.map_ofFn, Function.comp_def, hsample]

/-- The prefix-defined boundary uses the same conjugated bundle increments
as the Haar-preserving state-coordinate map. -/
def sourceBundleBoundary {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (v : Fin h → N) (j : ℕ) : N :=
  n * wordPrefix (fun k => if hk : k < h then φ ⟨k, hk⟩ (v ⟨k, hk⟩) else 1) j

omit [TopologicalSpace N] in
@[simp] theorem sourceBundleBoundary_zero {h : ℕ} (n : N)
    (φ : Fin h → N ≃* N) (v : Fin h → N) : sourceBundleBoundary n φ v 0 = n := by
  simp only [sourceBundleBoundary, wordPrefix_zero, mul_one]

section BoundaryCoordinates

variable [MeasurableSpace N] [MeasurableMul₂ N] [MeasurableInv N]

omit [TopologicalSpace N] in
theorem sourceBundleBoundary_succ {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (v : Fin h → N) (i : Fin h) :
    sourceBundleBoundary n φ v (i.val + 1) =
      n * prefixCoordinateEquiv h (fun j => φ j (v j)) i := by
  let u := fun k => if hk : k < h then φ ⟨k, hk⟩ (v ⟨k, hk⟩) else 1
  change n * wordPrefix u (i.val + 1) = _
  rw [← prefixCoordinateEquiv_eq_wordPrefix u h i]
  have he : (fun j : Fin h => u j.val) = fun j => φ j (v j) := by
    funext j
    simp only [u, dite_eq_left j.isLt]
  rw [he]

omit [TopologicalSpace N] in
/-- The paths' boundary coordinates coincide with the coordinates of the
Haar-preserving source-state map. -/
theorem sourceBundleBoundary_eq_stateEquiv {h : ℕ} (n : N) (φ : Fin h → N ≃* N)
    (ψ : Fin h → N ≃ᵐ N) (hψ : ∀ i z, ψ i z = φ i z) (v : Fin h → N) (i : Fin h) :
    sourceBundleBoundary n φ v (i.val + 1) = sourceBundleStateEquiv h n ψ v i := by
  rw [sourceBundleBoundary_succ, sourceBundleStateEquiv_apply]
  apply congrArg (fun u : Fin h → N => n * prefixCoordinateEquiv h u i)
  funext j
  exact (hψ j (v j)).symm

end BoundaryCoordinates

theorem sampledBlockProducts_source_product {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (t : Fin (h * m + h * m) → ℝ) :
    sampledBlockProducts sample t = fun k => if hk : k < h then
      φ ⟨k, hk⟩ (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t ⟨k, hk⟩)
        else 1 := by
  funext k
  unfold sampledBlockProducts
  split_ifs with hk
  · exact sampledBlockWord_source_product lie Exp X s letters r φ sample hsample t ⟨k, hk⟩
  · rfl

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]

/-- Each source bundle has a controlled path with its exact two boundary
states, even when different bundles use different inner conjugations. -/
theorem successful_sourceBundle_block_path {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (ι : N →* G) (x d₀ : G) (A : Set N) (S : Set G) (i : Fin h)
    (d : Fin m → ℝ → G) (hd : ∀ j, Continuous (d j)) (hd₀ : ∀ j, d j 0 = 1)
    (hf : ∀ j : Fin m, Continuous (fun b => ι (sample (finProdFinEquiv (i, j)).val b)))
    (hf₀ : ∀ j : Fin m, ι (sample (finProdFinEquiv (i, j)).val 0) = 1)
    {B κ ρ : ℝ} (hB : 0 ≤ B) (hκ : 0 ≤ κ)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ j : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ →
      n * sample (finProdFinEquiv (i, j)).val b ∈ A →
      PathMetricBound (supportVisitPath (d j) (hd j) (hd₀ j)
        (fun t => ι (sample (finProdFinEquiv (i, j)).val t)) (hf j) (hf₀ j)
        (x * ι n) d₀ r b) B κ ∧
      ∀ t, supportVisitPath (d j) (hd j) (hd₀ j)
        (fun t => ι (sample (finProdFinEquiv (i, j)).val t)) (hf j) (hf₀ j)
        (x * ι n) d₀ r b t ∈ S)
    (hinj : Function.Injective ι)
    (n : N) (hn : n ∈ A) (t : Fin (h * m + h * m) → ℝ) (ht : ‖t‖ ≤ ρ)
    (hs : SwitchSuccessful (fun _ => A) 0 (h * m) n
      (sampledSwitchParameters sample (h * m) t)) :
    let boundary := sourceBundleBoundary n φ
      (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t)
    ∃ γ : Path (x * ι (boundary i.val) * d₀) (x * ι (boundary (i.val + 1)) * d₀),
      PathMetricBound γ (B * 2 ^ m) (κ * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  dsimp only
  obtain ⟨γ, hγ, hS⟩ := successful_sample_block_path ι x d₀ A S sample hsub i
    d hd hd₀ hf hf₀ r hB hκ hbase hstep hinj n hn t ht hs
  have hproducts := sampledBlockProducts_source_product lie Exp X s letters r φ sample hsample t
  have hblock := sampledBlockWord_source_product lie Exp X s letters r φ sample hsample t i
  have hstart : x * ι (sourceBundleBoundary n φ
      (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t) i.val) * d₀ =
        x * ι (n * wordPrefix (sampledBlockProducts sample t) i.val) * d₀ := by
    rw [sourceBundleBoundary, hproducts]
  have hend : x * ι (sourceBundleBoundary n φ
      (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t) (i.val + 1)) * d₀ =
        x * ι ((n * wordPrefix (sampledBlockProducts sample t) i.val) *
          (sampledBlockWord sample t i).prod) * d₀ := by
    rw [sourceBundleBoundary, wordPrefix_succ, ← hproducts, hblock]
    simp only [dite_eq_left i.isLt, mul_assoc]
  exact ⟨γ.cast hstart hend, hγ, hS⟩

end PolycyclicRecognition

end

end OAI
