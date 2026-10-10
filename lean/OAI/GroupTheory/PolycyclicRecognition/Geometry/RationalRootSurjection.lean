import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianFiniteRankRootCore
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TensorMultilinearGenerators

namespace OAI

/-! # Rational surjectivity from positive powers in the image -/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {A B : Type} [CommGroup A] [CommGroup B]

theorem rational_map_surjective_of_roots (f : A →* B)
    (hroot : ∀ b : B, ∃ n : ℕ, 0 < n ∧ b ^ n ∈ f.range) :
    Function.Surjective (f.toAdditive.toIntLinearMap.baseChange ℚ) := by
  let F := f.toAdditive.toIntLinearMap.baseChange ℚ
  have hunit (b : B) : scalarTensorUnit ℚ (Additive B) (Additive.ofMul b) ∈
      LinearMap.range F := by
    obtain ⟨n, hn, a, ha⟩ := hroot b
    have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    have hnmem : (n : ℚ) • scalarTensorUnit ℚ (Additive B) (Additive.ofMul b) ∈
        LinearMap.range F := by
      refine ⟨scalarTensorUnit ℚ (Additive A) (Additive.ofMul a), ?_⟩
      change (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (f a) = _
      rw [ha]
      change scalarTensorUnit ℚ (Additive B) (n • Additive.ofMul b) = _
      rw [map_nsmul, Nat.cast_smul_eq_nsmul]
    have h := (LinearMap.range F).smul_mem ((n : ℚ)⁻¹) hnmem
    simpa only [inv_smul_smul₀ hnQ] using h
  apply LinearMap.range_eq_top.mp
  suffices ∀ z, z ∈ LinearMap.range F from top_unique (fun z _ => this z)
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul r b =>
    simpa only [scalarTensorUnit_smul, ofMul_toMul] using
      (LinearMap.range F).smul_mem r (hunit b.toMul)
  | add x y hx hy => exact (LinearMap.range F).add_mem hx hy

theorem abelian_finite_rational_rank_of_rootCore (H : Subgroup A) (hH : H.FG)
    (hroot : ∀ a : A, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H) :
    Module.Finite ℚ (RationalAbelianSpace A) := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let : Module.Finite ℤ (Additive H) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  apply Module.Finite.of_surjective (H.subtype.toAdditive.toIntLinearMap.baseChange ℚ)
  apply rational_map_surjective_of_roots
  intro a
  obtain ⟨n, hn, hna⟩ := hroot a
  exact ⟨n, hn, ⟨⟨a ^ n, hna⟩, rfl⟩⟩

end PolycyclicRecognition

end

end OAI
