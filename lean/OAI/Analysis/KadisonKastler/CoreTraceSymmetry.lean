import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # The weakly closed vector symmetry used for the core trace

Its scalar formulation is linear in the operator and passes to weak
operator limits. An involutive antiunitary then turns it into the exact
tracial norm identity needed by the finite-window criterion.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coreTraceSymmetrySpace (C : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | ∀ η, inner ℂ η (T ξ) = inner ℂ ξ (T (C η))}
  zero_mem' := by intro η; simp
  add_mem' := by
    intro A B hA hB η
    simp only [add_apply, inner_add_right, hA η, hB η]
  smul_mem' := by
    intro z A hA η
    simp only [smul_apply, inner_smul_right, hA η]

theorem coreTraceSymmetry_norm (C : H ≃ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C)
    (ξ : H) (T : H →L[ℂ] H) (hT : T ∈ coreTraceSymmetrySpace C ξ) :
    ‖T ξ‖ = ‖(star T) ξ‖ := by
  have he : T ξ = C ((star T) ξ) := by
    apply ext_inner_left ℂ
    intro η
    have hc := conjugateIsometry_inner C (C η) ((star T) ξ)
    rw [hC η] at hc
    have hswap : star (inner ℂ (C η) ((star T) ξ)) =
        inner ℂ ((star T) ξ) (C η) := inner_conj_symm _ _
    rw [hswap] at hc
    change inner ℂ η (T ξ) = inner ℂ η (C ((star T) ξ))
    rw [hc, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact hT η
  rw [he, C.norm_map]

omit [CompleteSpace H] in
theorem coreTraceSymmetry_of_weak_limit
    (C : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) {ι : Type*} {l : Filter ι} [NeBot l]
    (A : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hA : ∀ i, A i ∈ coreTraceSymmetrySpace C ξ)
    (hlim : ∀ x y, Tendsto (fun i => inner ℂ y (A i x)) l (𝓝 (inner ℂ y (T x)))) :
    T ∈ coreTraceSymmetrySpace C ξ := by
  intro η
  exact tendsto_nhds_unique (hlim ξ η)
    ((hlim (C η) ξ).congr' (Eventually.of_forall fun i => (hA i η).symm))

end

end KadisonKastler

end OAI
