import OAI.GroupTheory.PolycyclicRecognition.Algebra.RecurrentSourceBundles
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GroupedGoodWords

namespace OAI

/-! # Successful global switches give good conjugated bundle-end states -/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped Manifold

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  [MeasurableMul₂ G] [MeasurableInv G]

omit [Fintype I] [BorelSpace G] in
theorem successful_sourceBundleStates_good {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → G ≃* G) (sample : ℕ → ℝ → G)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (Good : Set G) (x : G) (hx : x ∈ Good)
    (t : Fin (h * m + h * m) → ℝ)
    (hs : SwitchSuccessful (fun _ => Good) 0 (h * m) x
      (sampledSwitchParameters sample (h * m) t)) :
    ∀ i : Fin h, x * prefixCoordinateEquiv h
      (fun j => φ j (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t j)) i ∈ Good := by
  have hg := (wordSheetsGood_sampled Good sample hsub (h * m) t x hx hs).bundle_products
  have he (i : Fin h) :
      (List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
        (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))).prod =
        φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) := by
    simp only [sourceBundleProduct, bundleParameterChart_left, bundleParameterChart_right,
      map_list_prod, List.map_ofFn, Function.comp_def, hsample]
  have he' : (fun i : Fin h =>
      (List.ofFn (fun j : Fin m => sample (finProdFinEquiv (i, j)).val
        (t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))))).prod) =
        fun i => φ i (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t i) :=
    funext he
  rw [he'] at hg
  exact hg.prefix_states

omit [Fintype I] [BorelSpace G] in
theorem sourceBundleState_last_eq_switchEndpoint {m h : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin (h + 1) → G ≃* G) (sample : ℕ → ℝ → G)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin (h + 1)) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (x : G) (t : Fin ((h + 1) * m + (h + 1) * m) → ℝ) :
    x * prefixCoordinateEquiv (h + 1)
      (fun j => φ j (sourceBundleProduct lie Exp X s letters
        (bundleParameterChart (h + 1) m) r t j)) (Fin.last h) =
      switchEndpoint ((h + 1) * m) x
        (sampledSwitchParameters sample ((h + 1) * m) t) := by
  rw [prefixCoordinateEquiv_last, sampledSwitchEndpoint_eq sample _ hsub]
  congr 1
  rw [ofFn_eq_flatten_bundles, List.prod_flatten, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_def, sourceBundleProduct, bundleParameterChart_left,
    bundleParameterChart_right, map_list_prod, List.map_ofFn, hsample]

end PolycyclicRecognition

end

end OAI
