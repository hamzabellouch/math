import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry6
import OAI.Analysis.Commutator.StageDensity
import OAI.Analysis.Commutator.WordPermutations
import OAI.Analysis.Commutator.WordTopology3

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {k l : ℕ}

include h1 in
theorem word_intertwiner (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
    wordSpace (fullSpace τ) (zeroSpace τ) l)
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hd : Dense (⋃ n, stageSet τ I φ n))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c₀ : (Fin k ≃ Fin l) → ℂ,
      Y = ∑ b : Fin k ≃ Fin l, c₀ b •
        (wordReindex (fullSpace τ) (zeroSpace τ) b).toContinuousLinearMap := by
  classical
  obtain ⟨c₀, hc₀⟩ := stageWord_inner_classification τ hτ h1 Y I φ e he hsize hY hleft
  refine ⟨c₀, ?_⟩
  apply operator_ext_dense_stages (fullSpace τ) (zeroSpace τ) k l
    (stageSet τ I φ) (centeredStageSet τ I φ)
    (stageSet_mono τ I φ e he) (centeredStageSet_mono τ I φ e he)
    hd (dense_centeredStageSet τ I φ hd)
  intro n d hd x hx c hc y hy
  obtain ⟨d, rfl⟩ := hd
  obtain ⟨c, rfl⟩ := hc
  choose a ha hax using hx
  choose b hb hby using hy
  have hxa : x = fun i => centeredStageVector τ (φ n) (a i) := funext (fun i => (hax i).symm)
  have hyb : y = fun i => centeredStageVector τ (φ n) (b i) := funext (fun i => (hby i).symm)
  rw [hxa, hyb, hc₀ n d c a b ha hb]
  simp only [sum_apply, smul_apply,
    inner_sum, inner_smul_right, LinearIsometry.coe_toContinuousLinearMap, wordReindex_inner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Kadison.TracialGNS
end

end OAI
