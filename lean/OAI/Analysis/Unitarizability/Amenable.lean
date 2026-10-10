import Mathlib
import OAI.Analysis.Unitarizability.AveragedForm

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

theorem representation_similar {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hG : Amenable G) (π : G →* (H →L[ℂ] H))
    (hb : ∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) : SimilarToUnitary π := by
  obtain ⟨m, h1, hp, hinv⟩ := hG
  obtain ⟨C, hC⟩ := hb
  let M : ℝ := max C 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hπ : ∀ g, ‖π g‖ ≤ M := fun g => (hC g).trans (le_max_left _ _)
  let B : H →L⋆[ℂ] H →L[ℂ] ℂ := (averagedForm π hM.le hπ m).mkContinuous₂
    (2 * M^2) (averagedForm_bound π hM.le hπ m h1 hp)
  let Q : H →L[ℂ] H := InnerProductSpace.continuousLinearMapOfBilin B
  have hQ (x y : H) : inner ℂ (Q x) y = m (coefficient π hM.le hπ x y) := by
    exact InnerProductSpace.continuousLinearMapOfBilin_apply B x y
  have hQpos : Q.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    rw [hQ]
    have h := averagedForm_nonneg π hM.le hπ m hp x
    refine ⟨?_, h.1⟩
    apply Complex.ext <;> simp [h.2]
  have hQnonneg : 0 ≤ Q := ContinuousLinearMap.nonneg_iff_isPositive.mpr hQpos
  have hunit : IsUnit Q := by
    apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map Q
      (c := ⟨(M^2)⁻¹, inv_nonneg.mpr (sq_nonneg M)⟩)
        (by change (0 : ℝ) < (M^2)⁻¹; positivity)
    intro x
    change ‖x‖^2 * (M^2)⁻¹ ≤ _
    rw [hQ]
    calc
      ‖x‖^2 * (M^2)⁻¹ ≤ (m (coefficient π hM.le hπ x x)).re := by
        rw [← div_eq_mul_inv, div_le_iff₀ (sq_pos_of_pos hM)]
        simpa only [mul_comm] using averagedForm_lower π hM.le hπ m h1 hp x
      _ ≤ ‖m (coefficient π hM.le hπ x x)‖ := Complex.re_le_norm _
  obtain ⟨s, hs⟩ := (CFC.isUnit_sqrt_iff Q hQnonneg).mpr hunit
  let S : H ≃L[ℂ] H := ContinuousLinearEquiv.ofUnit s
  have hS (x : H) : S x = CFC.sqrt Q x := by
    change (s : H →L[ℂ] H) x = _
    rw [hs]
  have hSsymmetric := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (CFC.sqrt_nonneg Q)).isSymmetric
  have hdiag (x : H) : ‖S x‖^2 = (m (coefficient π hM.le hπ x x)).re := by
    rw [hS, ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    have heq : inner ℂ (CFC.sqrt Q x) (CFC.sqrt Q x) = inner ℂ (Q x) x := by
      calc
        _ = inner ℂ (CFC.sqrt Q (CFC.sqrt Q x)) x := (hSsymmetric _ _).symm
        _ = inner ℂ (Q x) x := by
          congr 1
          exact congrArg (fun T : H →L[ℂ] H => T x) (CFC.sqrt_mul_sqrt_self Q hQnonneg)
    rw [heq, hQ, RCLike.re_to_complex]
  refine ⟨S, ?_⟩
  intro g x
  have hequal : ‖S (π g (S.symm x))‖^2 = ‖x‖^2 := by
    rw [hdiag, coefficient_translate, hinv, ← hdiag, S.apply_symm_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hequal

end DayDixmier

universe v
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  
theorem amenable_unitarizable (hG : Amenable G) : Unitarizable.{_, v} G := by
  intro H _ _ _ π hπ
  exact DayDixmier.representation_similar hG π hπ

end Dixmier
end

end OAI
