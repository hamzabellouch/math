import OAI.Analysis.KadisonKastler.NormUltraproductDerivation

namespace OAI

/-! # Approximate invariance gives exact invariance in the norm ultraproduct -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

theorem exists_normNull_commutator_approximation
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (hφ : ∀ j, Function.Injective (φ j))
    (ω : Ultrafilter ℕ)
    (T : VaryingBoundedSequence C) (ε : ℕ → ℝ)
    (hε : Tendsto ε (ω : Filter ℕ) (𝓝 0))
    (hε0 : ∀ j, 0 ≤ ε j) {K : ℝ} (hK : ∀ j, ε j ≤ K)
    (happrox : ∀ j (x : B j), ∃ y : B j,
      ‖T j * φ j x - φ j x * T j - φ j y‖ ≤ ε j * ‖x‖)
    (X : VaryingBoundedSequence B) :
    ∃ Y : VaryingBoundedSequence B,
      NormNullSequence C ω (T * normProductMap φ X - normProductMap φ X * T -
        normProductMap φ Y) := by
  choose y hy using fun j => happrox j (X j)
  have hX : ∀ j, ‖φ j (X j)‖ ≤ ‖X‖ := fun j =>
    (NonUnitalStarAlgHom.norm_apply_le (φ j) _).trans (varyingSequence_norm_apply_le X j)
  have hcomm : ∀ j, ‖T j * φ j (X j) - φ j (X j) * T j‖ ≤ 2 * ‖T‖ * ‖X‖ := by
    intro j
    calc
      _ ≤ ‖T j‖ * ‖φ j (X j)‖ + ‖φ j (X j)‖ * ‖T j‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖T‖ * ‖X‖ + ‖X‖ * ‖T‖ := by
        gcongr <;> first | exact hX j | exact varyingSequence_norm_apply_le T j
      _ = 2 * ‖T‖ * ‖X‖ := by ring
  have hyBound : ∀ j, ‖y j‖ ≤ (2 * ‖T‖ + K) * ‖X‖ := by
    intro j
    rw [← NonUnitalStarAlgHom.norm_map (φ j) (hφ j) (y j)]
    calc
      ‖φ j (y j)‖ ≤ ‖T j * φ j (X j) - φ j (X j) * T j‖ +
          ‖T j * φ j (X j) - φ j (X j) * T j - φ j (y j)‖ := by
        simpa only [sub_sub_cancel] using
          norm_sub_le (T j * φ j (X j) - φ j (X j) * T j)
            (T j * φ j (X j) - φ j (X j) * T j - φ j (y j))
      _ ≤ 2 * ‖T‖ * ‖X‖ + ε j * ‖X j‖ := add_le_add (hcomm j) (hy j)
      _ ≤ 2 * ‖T‖ * ‖X‖ + K * ‖X‖ := by
        exact add_le_add le_rfl (mul_le_mul (hK j) (varyingSequence_norm_apply_le X j)
          (norm_nonneg _) ((hε0 j).trans (hK j)))
      _ = (2 * ‖T‖ + K) * ‖X‖ := by ring
  let Y : VaryingBoundedSequence B :=
    ⟨y, memℓp_infty ⟨(2 * ‖T‖ + K) * ‖X‖, by
      rintro _ ⟨j, rfl⟩
      exact hyBound j⟩⟩
  refine ⟨Y, ?_⟩
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => (hy j).trans (mul_le_mul_of_nonneg_left
      (varyingSequence_norm_apply_le X j) (hε0 j)))
  simpa only [zero_mul] using hε.mul_const ‖X‖

end

end KadisonKastler

end OAI
