import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthNoFreePair
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialGrowthLinearImage

namespace OAI

/-! # The concrete polynomial-growth matrix image has no free pair -/
noncomputable section
namespace PolycyclicRecognition
variable {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]

theorem polynomial_growth_surjective_image (f : G →* H) (hf : Function.Surjective f)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (C d : ℕ)
    (hvol : ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    (∀ s ∈ S.image f, s⁻¹ ∈ S.image f) ∧
    Subgroup.closure ((S.image f : Finset H) : Set H) = ⊤ ∧
    ∀ n, (wordBall (S.image f) n).card ≤ C * (1 + n) ^ d := by
  refine ⟨?_, ?_, fun n => (wordBall_image_card_le f S n).trans (hvol n)⟩
  · intro s hs
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_image.mpr ⟨g⁻¹, hS g hg, map_inv f g⟩
  · rw [Finset.coe_image, ← f.map_closure, hgen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr hf

theorem polynomial_growth_image_no_free_pair (f : G →* H)
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    ∃ T : Finset f.range, (∀ t ∈ T, t⁻¹ ∈ T) ∧
      Subgroup.closure (T : Set f.range) = ⊤ ∧
      (∃ C d : ℕ, ∀ n, (wordBall T n).card ≤ C * (1 + n) ^ d) ∧
      ∀ j : FreeGroup Bool →* f.range, ¬Function.Injective j := by
  classical
  obtain ⟨C, d, hvol⟩ := hvol
  obtain ⟨hT, hTgen, hTvol⟩ := polynomial_growth_surjective_image
    f.rangeRestrict f.rangeRestrict_surjective S hS hgen C d hvol
  refine ⟨S.image f.rangeRestrict, hT, hTgen, ⟨C, d, hTvol⟩, ?_⟩
  exact polynomial_growth_no_free_pair _ hT hTgen ⟨C, d, hTvol⟩

omit [Group H] [DecidableEq H] in
theorem polynomial_growth_linear_image_no_free_pair [Infinite G]
    (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hvol : ∃ C d : ℕ, ∀ n, (wordBall S n).card ≤ C * (1 + n) ^ d) :
    ∃ n : ℕ, ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin n) ℝ,
      (Set.range ρ).Infinite ∧
      ∃ T : Finset ρ.range, (∀ t ∈ T, t⁻¹ ∈ T) ∧
        Subgroup.closure (T : Set ρ.range) = ⊤ ∧
        (∃ C d : ℕ, ∀ k, (wordBall T k).card ≤ C * (1 + k) ^ d) ∧
        ∀ j : FreeGroup Bool →* ρ.range, ¬Function.Injective j := by
  classical
  obtain ⟨n, ρ, hρ⟩ := polynomial_growth_infinite_real_linear_image S hS hgen hvol
  exact ⟨n, ρ, hρ, polynomial_growth_image_no_free_pair ρ S hS hgen hvol⟩

end PolycyclicRecognition

end

end OAI
