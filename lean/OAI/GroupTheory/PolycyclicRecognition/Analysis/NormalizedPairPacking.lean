import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactPairs
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation

namespace OAI

/-! # Separation and paths under an actual normalized pair -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal

variable {G : Type*} [Group G] [MetricSpace G] {Λ : ℝ≥0}

/-- The lower metric inequality turns this fixed source separation into
unit separation in the image. -/
theorem normalizedPair_image_dist_gt_one (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) {x y : G}
    (hxy : (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    1 < dist (p.val.1 x) (p.val.1 y) := by
  have hi : 0 < (Λ : ℝ)⁻¹ := inv_pos.mpr hΛ
  calc
    1 = (Λ : ℝ)⁻¹ * ((Λ : ℝ) * ((Λ : ℝ) + 1)) - Λ := by field_simp; ring
    _ < (Λ : ℝ)⁻¹ * dist x y - Λ := sub_lt_sub_right (mul_lt_mul_of_pos_left hxy hi) _
    _ ≤ _ := p.property.1.2.2.1 x y

section Finite

variable [DecidableEq G]

/-- The image of a sufficiently separated finite set has the same cardinality. -/
theorem normalizedPair_card_image (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    (s.image p.val.1).card = s.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro x hx y hy he
  by_contra hne
  have h := normalizedPair_image_dist_gt_one p hΛ (hsep x hx y hy hne)
  rw [he, dist_self] at h
  linarith

/-- Unit separation is preserved on the image finite set. -/
theorem normalizedPair_image_separated (p : NormalizedPair G Λ)
    (hΛ : 0 < (Λ : ℝ)) (s : Finset G)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (Λ : ℝ) * ((Λ : ℝ) + 1) < dist x y) :
    ∀ x ∈ s.image p.val.1, ∀ y ∈ s.image p.val.1, x ≠ y → 1 ≤ dist x y := by
  classical
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  have hab : a ≠ b := fun he => hxy (congrArg p.val.1 he)
  exact (normalizedPair_image_dist_gt_one p hΛ (hsep a ha b hb hab)).le

end Finite

/-- The image path is based at the identity by normalization, and both
coarse metric constants are multiplied by the same Lipschitz constant. -/
theorem normalizedPair_map_path (p : NormalizedPair G Λ) {g : G}
    (γ : Path (1 : G) g) {L κ : ℝ} (hγ : PathMetricBound γ L κ) :
    ∃ η : Path (1 : G) (p.val.1 g),
      (∀ t, η t = p.val.1 (γ t)) ∧ PathMetricBound η (Λ * L) (Λ * κ) := by
  let η := (γ.map p.val.1.continuous).cast p.property.2.symm rfl
  refine ⟨η, (fun _ => rfl), ?_⟩
  intro s t
  change dist (p.val.1 (γ s)) (p.val.1 (γ t)) ≤ _
  calc
    _ ≤ (Λ : ℝ) * dist (γ s) (γ t) := p.property.1.1.dist_le_mul _ _
    _ ≤ (Λ : ℝ) * (L * |(s : ℝ) - t| + κ) :=
      mul_le_mul_of_nonneg_left (hγ s t) Λ.coe_nonneg
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
