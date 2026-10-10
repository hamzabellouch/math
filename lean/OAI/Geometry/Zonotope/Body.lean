import OAI.Geometry.Zonotope.Support
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Set
open scoped Pointwise

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

lemma isClosed_centered : IsClosed (centered : Set (ι → ℝ)) := by
  have hs : (centered : Set (ι → ℝ)) =
      {x | ∀ i, |x i| ≤ 1} ∩ {x | ∀ i j, |x i - x j| ≤ 1} := by
    ext x
    exact mem_centered_iff x
  rw [hs]
  apply IsClosed.inter
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i).abs continuous_const
  · simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le ((continuous_apply i).sub (continuous_apply j)).abs continuous_const

lemma isCompact_centered : IsCompact (centered : Set (ι → ℝ)) := by
  apply (isCompact_Icc : IsCompact (Icc (-1 : ι → ℝ) 1)).of_isClosed_subset
    isClosed_centered
  intro x hx
  have h := (mem_centered_iff x).mp hx
  exact ⟨fun i => (abs_le.mp (h.1 i)).1, fun i => (abs_le.mp (h.1 i)).2⟩

lemma abs_convex_combination {x y a b : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : |a * x + b * y| ≤ 1 := by
  apply abs_le.mpr
  have hxl := mul_le_mul_of_nonneg_left (abs_le.mp hx).1 ha
  have hxu := mul_le_mul_of_nonneg_left (abs_le.mp hx).2 ha
  have hyl := mul_le_mul_of_nonneg_left (abs_le.mp hy).1 hb
  have hyu := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 hb
  constructor <;> linarith

lemma convex_centered : Convex ℝ (centered : Set (ι → ℝ)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_centered_iff] at hx hy ⊢
  constructor
  · intro i
    exact abs_convex_combination (hx.1 i) (hy.1 i) ha hb hab
  · intro i j
    have h := abs_convex_combination (hx.2 i j) (hy.2 i j) ha hb hab
    have heq : (a • x + b • y) i - (a • x + b • y) j =
        a * (x i - x j) + b * (y i - y j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact h

lemma half_box_subset_centered :
    {x : ι → ℝ | ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2} ⊆ centered := by
  intro x hx
  apply (mem_centered_iff x).mpr
  constructor
  · intro i
    apply abs_le.mpr
    constructor <;> linarith [hx i]
  · intro i j
    apply abs_le.mpr
    constructor <;> linarith [hx i, hx j]

lemma centered_interior_nonempty : (interior (centered : Set (ι → ℝ))).Nonempty := by
  let U : Set (ι → ℝ) := {x | ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2}
  have ho : IsOpen U := by
    dsimp [U]
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_apply i) continuous_const)
  refine ⟨0, interior_mono half_box_subset_centered ?_⟩
  change (0 : ι → ℝ) ∈ interior U
  rw [ho.interior_eq]
  intro i
  norm_num

lemma isCompact_scaled_centered (c : ℝ) :
    IsCompact ((fun y : ι → ℝ => c • y) '' centered) :=
  isCompact_centered.smul c

lemma convex_scaled_centered (c : ℝ) :
    Convex ℝ ((fun y : ι → ℝ => c • y) '' centered) :=
  convex_centered.smul c

lemma scaled_centered_interior_nonempty (c : ℝ) (hc : c ≠ 0) :
    (interior ((fun y : ι → ℝ => c • y) '' centered)).Nonempty := by
  change (interior (c • (centered : Set (ι → ℝ)))).Nonempty
  rw [interior_smul₀ hc]
  exact centered_interior_nonempty.image _

end DiagonalZonotope

end

end OAI
