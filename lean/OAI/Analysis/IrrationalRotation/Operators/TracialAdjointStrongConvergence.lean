import OAI.Analysis.IrrationalRotation.Analysis.SeparatingVectorStrongConvergence

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {ξ : H}

theorem IsFaithfulTracialVector.norm_star_apply_eq
    (htrace : IsFaithfulTracialVector M ξ) {A : H →L[ℂ] H} (hA : A ∈ M) :
    ‖(star A) ξ‖ = ‖A ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hnorm (T : H →L[ℂ] H) :
      ‖T ξ‖ ^ 2 = (vectorTrace ξ (star T * T)).re := by
    exact T.apply_norm_sq_eq_inner_adjoint_right ξ
  rw [hnorm, hnorm, star_star]
  exact congrArg Complex.re (htrace.2.1 A (star A) hA (star_mem hA))

theorem IsFaithfulTracialVector.norm_star_sub_apply_eq
    (htrace : IsFaithfulTracialVector M ξ) {A B : H →L[ℂ] H}
    (hA : A ∈ M) (hB : B ∈ M) :
    ‖(star A) ξ - (star B) ξ‖ = ‖A ξ - B ξ‖ := by
  simpa only [star_sub, sub_apply] using
    htrace.norm_star_apply_eq (sub_mem hA hB)

theorem IsFaithfulTracialVector.strong_tendsto_star_of_bounded
    {ι : Type*} {l : Filter ι} (htrace : IsFaithfulTracialVector M ξ)
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H} {C : ℝ}
    (hA : ∀ i, A i ∈ M) (hB : B ∈ M)
    (hξ : Tendsto (fun i => A i ξ) l (𝓝 (B ξ)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (v : H) :
    Tendsto (fun i => (star (A i)) v) l (𝓝 ((star B) v)) := by
  apply htrace.strong_tendsto_of_bounded (C := C) (fun i => star_mem (hA i)) (star_mem hB) ?_ ?_ v
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [htrace.norm_star_sub_apply_eq (hA _) hB] using
      tendsto_iff_norm_sub_tendsto_zero.mp hξ
  · simpa only [norm_star] using hC

theorem IsFaithfulTracialVector.strongStar_tendsto_of_bounded
    {ι : Type*} {l : Filter ι} (htrace : IsFaithfulTracialVector M ξ)
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H} {C : ℝ}
    (hA : ∀ i, A i ∈ M) (hB : B ∈ M)
    (hξ : Tendsto (fun i => A i ξ) l (𝓝 (B ξ)))
    (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) :
    (∀ v : H, Tendsto (fun i => A i v) l (𝓝 (B v))) ∧
      (∀ v : H, Tendsto (fun i => (star (A i)) v) l (𝓝 ((star B) v))) :=
  ⟨htrace.strong_tendsto_of_bounded hA hB hξ hC,
    htrace.strong_tendsto_star_of_bounded hA hB hξ hC⟩

end Invariant233

end

end OAI
