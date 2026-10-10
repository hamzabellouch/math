import OAI.Analysis.KadisonKastler.CentralVectorMatrixLimit
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Dense finite tests force a central line

The finite-dimensional refinement estimates pass through the projection
onto the common central-vector space. Vanishing errors on a dense family
then force its entire range into a single line.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem projection_range_line_of_dense_tests
    (K : Submodule ℂ H) [CompleteSpace K]
    (L : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (L n)]
    (hKL : ∀ n, K ≤ L n) (ξ : H) (η : ℕ → H) (hdense : DenseRange η)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(L n).starProjection (η i) - c • (L n).starProjection ξ‖ ≤ ε n) :
    K ≤ Submodule.span ℂ {K.starProjection ξ} := by
  let S := Submodule.span ℂ {K.starProjection ξ}
  have hS : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have htest' (i : ℕ) : K.starProjection (η i) ∈ S := by
    apply closure_minimal (fun _ h => h) hS
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨n,hn,hi⟩ := ((hε.eventually (gt_mem_nhds hδ)).and
      (eventually_ge_atTop i)).exists
    obtain ⟨c,hc⟩ := htest n i hi
    refine ⟨c • K.starProjection ξ, S.smul_mem c (Submodule.subset_span (by simp)), ?_⟩
    have hcomp : K.starProjection ∘L (L n).starProjection = K.starProjection :=
      Submodule.starProjection_comp_starProjection_of_le (hKL n)
    have he : K.starProjection ((L n).starProjection (η i) -
        c • (L n).starProjection ξ) = K.starProjection (η i) - c • K.starProjection ξ := by
      rw [map_sub, map_smul]
      have h1 := congrArg (fun T : H →L[ℂ] H => T (η i)) hcomp
      have h2 := congrArg (fun T : H →L[ℂ] H => T ξ) hcomp
      change K.starProjection ((L n).starProjection (η i)) = K.starProjection (η i) at h1
      change K.starProjection ((L n).starProjection ξ) = K.starProjection ξ at h2
      rw [h1,h2]
    rw [dist_eq_norm, ← he]
    exact ((K.norm_starProjection_apply_le _).trans hc).trans_lt hn
  have hclosed : IsClosed {x : H | K.starProjection x ∈ S} := hS.preimage K.starProjection.continuous
  have hall (x : H) : K.starProjection x ∈ S :=
    (closure_minimal (by rintro _ ⟨i,rfl⟩; exact htest' i) hclosed) (hdense x)
  intro x hx
  have h := hall x
  rwa [Submodule.starProjection_eq_self_iff.mpr hx] at h

variable {M : VonNeumannAlgebra H}

/-- The finite central-vector tests used in the refinement construction
force the common central-vector space to be a line. -/
theorem matrixCentralVectorSpace_le_line_of_dense_tests
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (η : ℕ → H) (hdense : DenseRange η)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection (η i) -
        c • (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ ε n) :
    matrixCentralVectorSpace A J ≤
      Submodule.span ℂ {(matrixCentralVectorSpace A J).starProjection ξ} :=
  projection_range_line_of_dense_tests _ _ (matrixCentralVectorSpace_le A J) ξ η hdense ε hε htest

/-- The displacement bound survives the strong projection limit. -/
theorem matrixCentralVectorSpace_displacement_le
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (δ : ℝ)
    (hδ : ∀ n,
      ‖ξ - (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ δ) :
    ‖ξ - (matrixCentralVectorSpace A J).starProjection ξ‖ ≤ δ :=
  le_of_tendsto (tendsto_const_nhds.sub (matrixCentralVectorSpace_tendsto A hA J ξ)).norm
    (Eventually.of_forall hδ)

end

end KadisonKastler

end OAI
