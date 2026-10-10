import Mathlib
import OAI.Analysis.Commutator.FreeSymmetry7
import OAI.Analysis.Commutator.TensorMultiplicity2

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

open PreHilbert HilbertTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b) = τ (b*a)) (h1 : τ 1 = 1)

variable {k l : ℕ} {J K : Type*}
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

include h1 in
theorem word_multiplicity_slices
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hd : Dense (⋃ n, stageSet τ I φ n))
    (hT : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      T.comp (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap 1) =
        (HilbertTensor.map (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap 1).comp T)
    (hleft : ∀ a : A, T.comp (HilbertTensor.map (wordLeft τ a k) 1) =
      (HilbertTensor.map (wordLeft τ a l) 1).comp T) :
    ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap := by
  intro a b
  apply word_intertwiner τ hτ h1 (scalarSlice T a b) I φ e he hsize hd
  · intro n u
    exact scalarSlice_covariant T _ _ (hT n u) a b
  · intro x
    exact scalarSlice_covariant T _ _ (hleft x) a b

theorem word_multiplicity_offlevel
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) l ⊗[ℂ] K))
    (hkl : k ≠ l)
    (hclass : ∀ a : J, ∀ b : K, ∃ c : (Fin k ≃ Fin l) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap) : T = 0 := by
  classical
  let : IsEmpty (Fin k ≃ Fin l) := ⟨fun b => hkl (by simpa using Fintype.card_congr b)⟩
  apply eq_zero_of_scalarSlice
  intro a b
  obtain ⟨c, hc⟩ := hclass a b
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hc

include h1 in
theorem word_multiplicity_repeated [CompleteSpace J]
    (T : Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J) →L[ℂ]
      Completion (wordSpace (fullSpace τ) (zeroSpace τ) k ⊗[ℂ] J))
    (hclass : ∀ a b : J, ∃ c : Equiv.Perm (Fin k) → ℂ,
      scalarSlice T a b = ∑ σ, c σ •
        (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap)
    (z : zeroSpace τ) (hz : ‖z‖ = 1) :
    ∃ B : J →L[ℂ] J, ‖B‖ ≤ ‖T‖ ∧
      ∀ (d : fullSpace τ) (x : zeroSpace τ) (a : J),
        T (pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) a) =
          pair (word (fullSpace τ) (zeroSpace τ) k d (fun _ => x)) (B a) := by
  let v := word (fullSpace τ) (zeroSpace τ) k (vacuum τ) (fun _ => z)
  have hv : ‖v‖ = 1 := by
    simp only [v, norm_word, vacuum_norm τ h1, hz, Finset.prod_const_one, mul_one]
  refine ⟨multiplicityCompression T v, norm_multiplicityCompression_le T v hv, ?_⟩
  intro d x a
  apply repeated_pair T (fun σ : Equiv.Perm (Fin k) =>
    (wordReindex (fullSpace τ) (zeroSpace τ) σ).toContinuousLinearMap) hclass v _ hv
  · intro σ
    simp only [v, LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]
  · intro σ
    simp only [LinearIsometry.coe_toContinuousLinearMap, wordReindex_word, Function.comp_def]

end Kadison.TracialGNS
end

end OAI
