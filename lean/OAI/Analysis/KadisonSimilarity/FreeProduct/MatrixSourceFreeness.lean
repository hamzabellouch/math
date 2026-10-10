import OAI.Analysis.KadisonSimilarity.FreeProduct.NormalInclusionFreeness
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixDiffuseSource
import OAI.Analysis.KadisonSimilarity.Tracial.FiniteFactorApplication

namespace OAI

/-! The proved prescribed-source freeness theorem supplies every finite
matrix amplification required by the finite-factor estimate. -/

noncomputable section
namespace KadisonSimilarity
open UltrapowerBridge
open scoped ComplexOrder

universe u
variable {A B : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem matrix_gns_separable (τ : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τ.GNS] (n : ℕ) [NeZero n] :
    TopologicalSpace.SeparableSpace (normalizedMatrixTrace τ n).GNS := by
  let J := (matrixGNSUnitary τ n).symm
  have hs := TopologicalSpace.isSeparable_range J.continuous
  rw [Set.range_eq_univ.mpr J.surjective] at hs
  exact TopologicalSpace.isSeparable_univ_iff.mp hs

theorem finiteFactorFreeCornerInputs_of_normal_tower
    (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
    [TopologicalSpace.SeparableSpace τB.GNS]
    (hA : τA 1 = 1) (hB : τB 1 = 1)
    (trA : ∀ a b, τA (a * b) = τA (b * a))
    (trB : ∀ a b, τB (a * b) = τB (b * a))
    (hfA : ∀ a, τA (star a * a) = 0 → a = 0)
    (hfB : ∀ a, τB (star a * a) = 0 → a = 0)
    (hnA : HasNormalGNS τA) (hnB : HasNormalGNS τB)
    (φ : A →⋆ₐ[ℂ] B) (hi : Function.Injective φ)
    (ht : ∀ a, τB (φ a) = τA a)
    (hirr : ∀ c : B, (∀ a : A, φ a * c = c * φ a) → ∃ z : ℂ, c = z • 1)
    {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] [∀ j, Nonempty (I j)]
    (M : NestedTracialMatrices (A := I) τA.toLinearMap (gnsTracialVector τA))
    (hsize : Filter.Tendsto (fun j => (Fintype.card (I j) : ℝ)) Filter.atTop Filter.atTop)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite) :
    FiniteFactorFreeCornerInputs τA τB hA hB ω trA trB φ ht hω := by
  refine ⟨fun n _ => ?_⟩
  let := matrix_gns_separable τB n
  have hcenter : ∀ c : A, (∀ a : A, c * a = a * c) →
      ∃ z : ℂ, c = algebraMap ℂ A z := by
    intro c hc
    obtain ⟨z, hz⟩ := (gnsTracialGeometry τA trA).scalar_center_of_matrix_tower M
      (gnsTracialVector_injective τA hfA) c (fun a => (hc a).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hfactor : ∀ X : CStarMatrix (Fin n) (Fin n) A,
      (∀ Y, Y * X = X * Y) → ∃ z : ℂ, X = z • 1 := by
    intro X hX
    have hid (Y : CStarMatrix (Fin n) (Fin n) A) :
        matrixEntryHom (StarAlgHom.id ℂ A) Y = Y := by
      ext i j
      rfl
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant (StarAlgHom.id ℂ A)
      hcenter X (fun Y => by rw [hid]; exact (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hirrn : ∀ X : CStarMatrix (Fin n) (Fin n) B,
      (∀ Y, matrixEntryHom φ Y * X = X * matrixEntryHom φ Y) →
      ∃ z : ℂ, X = z • 1 := by
    intro X hX
    obtain ⟨z, hz⟩ := scalar_of_matrix_relative_commutant φ
      (fun c hc => by
        obtain ⟨z, hz⟩ := hirr c (fun a => (hc a).symm)
        exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩)
      X (fun Y => (hX Y).symm)
    exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  exact popa1995_of_normal_traces (normalizedMatrixTrace τA n) (normalizedMatrixTrace τB n)
    (matrix_trace_balls_closed τA _ hnA n hA trA hfA)
    (normalizedMatrixTrace_one τA hA) (normalizedMatrixTrace_one τB hB)
    (normalizedMatrixTrace_tracial τA trA) (normalizedMatrixTrace_tracial τB trB)
    (normalizedMatrixTrace_faithful τB hfB) (matrix_gns_normal_range τB _ hnB n)
    (matrixEntryHom φ) (matrixEntryHom_injective φ hi)
    (normalizedMatrixTrace_entryHom τA τB φ ht) hfactor
    (matrix_diffuse_of_tower τA hA trA hfA M hnA hsize n) hirrn ω hω (matrixDiagonalHom n)

end KadisonSimilarity

end

end OAI
