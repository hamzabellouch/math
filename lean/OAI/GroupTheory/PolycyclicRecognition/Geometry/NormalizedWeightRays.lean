import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightRayPermutation
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! # Deduplicating positive weight rays

Unit normalization gives a concrete finite set of positive rays, even when
the original generator list repeats some rays with different multiplicities.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def normalizedWeight (φ : W →L[ℝ] ℝ) : W →L[ℝ] ℝ := ‖φ‖⁻¹ • φ

def NormalizedWeightRays (α : I → W →L[ℝ] ℝ) :=
  ↥(Set.range fun i => normalizedWeight (α i))

instance (α : I → W →L[ℝ] ℝ) : Finite (NormalizedWeightRays α) :=
  (Set.finite_range _).to_subtype

theorem norm_normalizedWeight (φ : W →L[ℝ] ℝ) (hφ : φ ≠ 0) :
    ‖normalizedWeight φ‖ = 1 := by
  simp [normalizedWeight, norm_smul, norm_ne_zero_iff.mpr hφ]

theorem normalizedWeight_pos_iff (φ : W →L[ℝ] ℝ) (hφ : φ ≠ 0) (w : W) :
    0 < normalizedWeight φ w ↔ 0 < φ w := by
  change 0 < ‖φ‖⁻¹ * φ w ↔ _
  exact mul_pos_iff_of_pos_left (inv_pos.mpr (norm_pos_iff.mpr hφ))

omit [Fintype I] in
theorem normalizedWeightRays_distinct (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0)
    (x y : NormalizedWeightRays α) (r : ℝ) (hr : 0 < r)
    (heq : x.val.toLinearMap = r • y.val.toLinearMap) : x = y := by
  have hx : ‖x.val‖ = 1 := by
    obtain ⟨i, hi⟩ := x.property
    rw [← hi]
    exact norm_normalizedWeight _ (hα i)
  have hy : ‖y.val‖ = 1 := by
    obtain ⟨i, hi⟩ := y.property
    rw [← hi]
    exact norm_normalizedWeight _ (hα i)
  have heq' : x.val = r • y.val := by
    ext w
    exact LinearMap.congr_fun heq w
  have hnorm := congrArg norm heq'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, hy, mul_one] at hnorm
  apply Subtype.ext
  simpa only [← hnorm, one_smul] using heq'

/-- A pullback on the original weights induces a permutation of the actual
distinct rays, independently of duplicate generator weights. -/
theorem exists_normalizedWeightRays_permutation
    (α : I → W →L[ℝ] ℝ) (hα : ∀ i, α i ≠ 0) (A : W ≃ₗ[ℝ] W)
    (hmaps : ∀ i, ∃ (j : I) (r : ℝ), 0 < r ∧
      (α i).toLinearMap.comp A.toLinearMap = r • (α j).toLinearMap) :
    ∃ σ : NormalizedWeightRays α ≃ NormalizedWeightRays α,
      ∃ r : NormalizedWeightRays α → ℝ, (∀ x, 0 < r x) ∧
        ∀ x, x.val.toLinearMap.comp A.toLinearMap = r x • (σ x).val.toLinearMap := by
  let : Fintype (NormalizedWeightRays α) := Fintype.ofFinite _
  apply exists_weight_ray_permutation (fun x : NormalizedWeightRays α => x.val.toLinearMap)
    A (normalizedWeightRays_distinct α hα)
  intro x
  obtain ⟨i, hi⟩ := x.property
  obtain ⟨j, r, hr, hij⟩ := hmaps i
  let y : NormalizedWeightRays α := ⟨normalizedWeight (α j), ⟨j, rfl⟩⟩
  refine ⟨y, ‖α i‖⁻¹ * r * ‖α j‖, ?_, ?_⟩
  · exact mul_pos (mul_pos (inv_pos.mpr (norm_pos_iff.mpr (hα i))) hr)
      (norm_pos_iff.mpr (hα j))
  · ext w
    have hh := LinearMap.congr_fun hij w
    change α i (A w) = r * α j w at hh
    change x.val (A w) = (‖α i‖⁻¹ * r * ‖α j‖) * y.val w
    rw [← hi]
    change ‖α i‖⁻¹ * α i (A w) =
      (‖α i‖⁻¹ * r * ‖α j‖) * (‖α j‖⁻¹ * α j w)
    rw [hh]
    field_simp [norm_ne_zero_iff.mpr (hα j)]

end PolycyclicRecognition

end

end OAI
