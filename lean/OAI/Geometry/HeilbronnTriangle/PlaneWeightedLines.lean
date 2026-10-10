import OAI.Geometry.HeilbronnTriangle.PlaneLineMatrices

namespace OAI


noncomputable section
namespace Problem355.PlaneLines
open scoped LinearAlgebra.Projectivization
variable {K V A : Type*} [Field K] [Finite K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [AddCommGroup A]

def subgroupFiber {α κ : Type*} (s : Finset α) (rows : α → κ → A)
    (Γ : AddSubgroup A) : Finset α := by
  classical
  exact s.filter fun a => ∀ i, rows a i ∈ Γ

theorem card_rank_one_family_le [Finite V] {α κ : Type*}
    (hV : Module.finrank K V = 2) (f : A →+ V) (hf : Function.Surjective f)
    (s : Finset α) (rows : α → κ → A) (B : ℝ)
    (hrank : ∀ a ∈ s,
      Module.finrank K (Submodule.span K (Set.range (fun i => f (rows a i)))) ≤ 1)
    (hcount : ∀ Γ : AddSubgroup A, Γ.index = Nat.card K →
      ((subgroupFiber s rows Γ).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ (Nat.card K + 1 : ℝ) * B := by
  classical
  apply PlaneLineMatrices.card_family_le_lines_mul_real hV s (fun a i => f (rows a i)) B hrank
  intro p
  exact hcount (p.submodule.toAddSubgroup.comap f) (line_preimage_index hV f hf p)

theorem sum_weights_rank_one_le [Finite V] {α κ : Type*}
    (hV : Module.finrank K V = 2) (f : A →+ V) (hf : Function.Surjective f)
    (s : Finset α) (rows : α → κ → A) (B W : ℝ) (hW : 0 ≤ W)
    (weight : α → ℝ) (hweight : ∀ a ∈ s, weight a ≤ W)
    (hrank : ∀ a ∈ s,
      Module.finrank K (Submodule.span K (Set.range (fun i => f (rows a i)))) ≤ 1)
    (hcount : ∀ Γ : AddSubgroup A, Γ.index = Nat.card K →
      ((subgroupFiber s rows Γ).card : ℝ) ≤ B) :
    ∑ a ∈ s, weight a ≤ (Nat.card K + 1 : ℝ) * B * W := by
  calc
    ∑ a ∈ s, weight a ≤ ∑ _a ∈ s, W := Finset.sum_le_sum hweight
    _ = (s.card : ℝ) * W := by simp
    _ ≤ (Nat.card K + 1 : ℝ) * B * W :=
      mul_le_mul_of_nonneg_right (card_rank_one_family_le hV f hf s rows B hrank hcount) hW

end Problem355.PlaneLines

end

end OAI
