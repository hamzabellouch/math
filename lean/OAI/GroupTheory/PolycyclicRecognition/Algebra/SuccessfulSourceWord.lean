import OAI.GroupTheory.PolycyclicRecognition.Analysis.SourceBundleBlockPaths
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GoodFiniteWordVertices

namespace OAI

/-! # Good conjugated words furnished by the successful bundle parameters -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Manifold

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace N] [ChartedSpace E N] [Group N]
  [LieGroup (𝓘(ℝ, E)) ⊤ N]

/-- Each global successful parameter gives exactly the good word needed
by the profile path construction on its own bundle sheet. -/
theorem successful_sourceBundle_word_good {h m : ℕ}
    (lie : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) N)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) N → N)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I) (r : ℝ)
    (φ : Fin h → N ≃* N) (sample : ℕ → ℝ → N)
    (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ (i : Fin h) (j : Fin m) t,
      sample (finProdFinEquiv (i, j)).val t = φ i
        (Exp (lie (t • (Real.exp (r * s (letters j)) • X (letters j))))))
    (Good : Set N) (initial : N) (hi : initial ∈ Good)
    (t : Fin (h * m + h * m) → ℝ)
    (hs : SwitchSuccessful (fun _ => Good) 0 (h * m) initial
      (sampledSwitchParameters sample (h * m) t)) (i : Fin h) :
    WordSheetsGood Good
      (sourceBundleBoundary initial φ
        (sourceBundleProduct lie Exp X s letters (bundleParameterChart h m) r t) i.val)
      (List.ofFn (fun j : Fin m => φ i (Exp (lie
        ((t (Fin.castAdd (h * m) (finProdFinEquiv (i, j))) -
          t (Fin.natAdd (h * m) (finProdFinEquiv (i, j)))) •
            (Real.exp (r * s (letters j)) • X (letters j))))))) := by
  let w : ℕ → List N := fun j =>
    if hj : j < h then sampledBlockWord sample t ⟨j, hj⟩ else []
  have hw : (fun j => (w j).prod) = sampledBlockProducts sample t := by
    funext j
    dsimp only [w, sampledBlockProducts]
    split_ifs <;> rfl
  have hg := wordSheetsGood_sampled Good sample hsub (h * m) t initial hi hs
  rw [ofFn_eq_flatten_bundles] at hg
  have hg' : WordSheetsGood Good initial (List.ofFn (fun j : Fin h => w j.val)).flatten := by
    simpa only [w, sampledBlockWord, dite_eq_left (Fin.isLt _)] using hg
  have hb := hg'.ofFn_block w i
  rw [hw, show w i.val = sampledBlockWord sample t i by simp only [w, dite_eq_left i.isLt]] at hb
  have hproducts := sampledBlockProducts_source_product lie Exp X s letters r φ sample hsample t
  change WordSheetsGood Good (initial * wordPrefix _ i.val) _
  rw [← hproducts]
  simpa only [sampledBlockWord, hsample] using hb

end PolycyclicRecognition

end

end OAI
