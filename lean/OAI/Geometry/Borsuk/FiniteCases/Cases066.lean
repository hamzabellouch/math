import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c25388 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {1, 3, 4} → ¬ T {1, 3, 6} → ¬ T {1, 3, 9} → False := by
  intro a289 n44 n46 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 8} {1, 3} {4, 6, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c25408 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 1, 9} → ¬ T {1, 3, 9} → ¬ T {1, 6, 9} → False := by
  intro a289 n8 n49 n61
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 8} {1, 9} {0, 3, 6} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n61 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) ht)

theorem c25430 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a289 n21 n49 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 8} {3, 9} {0, 1, 4} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c25474 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ T {0, 3, 8} → ¬ T {1, 4, 6} → False := by
  intro a290 n20 n51
  have hc := h.complementary {2, 5, 7, 9} {0, 3, 8} a290 (by decide) (by decide)
  have he : ( {2, 5, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n51)

theorem c25523 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a290 a2 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 9} {1, 3} {0, 4, 6} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c25579 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → T {0, 4, 6} → T {1, 4, 6} → T {3, 4, 6} → False := by
  intro a290 a23 a51 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 9} {4, 6} {0, 1, 3} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c25590 (h : TenSystem T Q) :
    Q {2, 5, 7, 9} → ¬ T {0, 4, 8} → ¬ T {3, 4, 8} → ¬ T {4, 6, 8} → False := by
  intro a290 n25 n89 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 9} {4, 8} {0, 3, 6} a290 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 8} = {3, 4, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)

theorem c25603 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {4, 6, 7} → False := by
  intro a291 a2 a105
  have hc := h.complementary {2, 5, 8, 9} {0, 1, 3} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a2 a105

theorem c25604 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 1, 4} → ¬ T {3, 6, 7} → False := by
  intro a291 n3 n95
  have hc := h.complementary {2, 5, 8, 9} {0, 1, 4} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n95)

theorem c25607 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 6} → T {3, 4, 7} → False := by
  intro a291 a5 a88
  have hc := h.complementary {2, 5, 8, 9} {0, 1, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a5 a88

theorem c25613 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 3, 6} → T {1, 4, 7} → False := by
  intro a291 a18 a52
  have hc := h.complementary {2, 5, 8, 9} {0, 3, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a18 a52

theorem c25616 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 6} → ¬ T {1, 3, 7} → False := by
  intro a291 n23 n47
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 3, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n47)

theorem c25617 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 4, 6} → T {1, 3, 7} → False := by
  intro a291 a23 a47
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 6} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a23 a47

theorem c25618 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 6} → False := by
  intro a291 n24 n46
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 7} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n46)

theorem c25619 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 4, 7} → T {1, 3, 6} → False := by
  intro a291 a24 a46
  have hc := h.complementary {2, 5, 8, 9} {0, 4, 7} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a24 a46

theorem c25621 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 6, 7} → T {1, 3, 4} → False := by
  intro a291 a31 a44
  have hc := h.complementary {2, 5, 8, 9} {0, 6, 7} a291 (by decide) (by decide)
  have he : ( {2, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a44

theorem c25625 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a291 a2 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {0, 1} {3, 4, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c25635 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 7} → False := by
  intro a291 a2 a18 a19
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {0, 3} {1, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)

theorem c25643 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a291 a3 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {0, 4} {1, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c25652 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 3, 6} → ¬ T {0, 4, 6} → ¬ T {0, 6, 7} → False := by
  intro a291 n18 n23 n31
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {0, 6} {3, 4, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) ht)
  · exact n31 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) ht)

theorem c25663 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a291 a2 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {1, 3} {0, 4, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c25667 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a291 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {1, 3} {0, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c25668 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {1, 3, 4} → ¬ T {1, 3, 6} → ¬ T {1, 3, 7} → False := by
  intro a291 n44 n46 n47
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {1, 3} {4, 6, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)

theorem c25702 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 3, 6} → ¬ T {1, 3, 6} → ¬ T {3, 4, 6} → False := by
  intro a291 n18 n46 n87
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {3, 6} {0, 1, 4} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 6} = {0, 3, 6} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)

theorem c25704 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 3, 6} → ¬ T {1, 3, 6} → ¬ T {3, 6, 7} → False := by
  intro a291 n18 n46 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {3, 6} {0, 1, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 6} = {0, 3, 6} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c25708 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {1, 3, 6} → ¬ T {3, 4, 6} → ¬ T {3, 6, 7} → False := by
  intro a291 n46 n87 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {3, 6} {1, 4, 7} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c25728 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n24 n52 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {4, 7} {0, 1, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c25730 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {4, 7} {0, 3, 6} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c25735 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a291 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 8, 9} {6, 7} {0, 1, 3} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c25738 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {6, 7} {0, 3, 4} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c25740 (h : TenSystem T Q) :
    Q {2, 5, 8, 9} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a291 n59 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 8, 9} {6, 7} {1, 3, 4} a291 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c25756 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → ¬ T {0, 4, 5} → ¬ T {1, 3, 9} → False := by
  intro a292 n22 n49
  have hc := h.complementary {2, 6, 7, 8} {0, 4, 5} a292 (by decide) (by decide)
  have he : ( {2, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n49)

theorem c25805 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a292 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {1, 3} {0, 4, 9} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c25807 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a292 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {1, 3} {0, 5, 9} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c25859 (h : TenSystem T Q) :
    Q {2, 6, 7, 8} → T {0, 4, 5} → T {1, 4, 5} → T {3, 4, 5} → False := by
  intro a292 a22 a50 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 7, 8} {4, 5} {0, 1, 3} a292 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

theorem c25883 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → T {0, 1, 3} → T {4, 5, 8} → False := by
  intro a293 a2 a103
  have hc := h.complementary {2, 6, 7, 9} {0, 1, 3} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a103

theorem c25885 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → T {0, 1, 4} → T {3, 5, 8} → False := by
  intro a293 a3 a93
  have hc := h.complementary {2, 6, 7, 9} {0, 1, 4} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a3 a93

theorem c25900 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 4} → False := by
  intro a293 n29 n44
  have hc := h.complementary {2, 6, 7, 9} {0, 5, 8} a293 (by decide) (by decide)
  have he : ( {2, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n44)

theorem c26016 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a293 n29 n57 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 6, 7, 9} {5, 8} {0, 1, 4} a293 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c26018 (h : TenSystem T Q) :
    Q {2, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a293 n29 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 6, 7, 9} {5, 8} {0, 3, 4} a293 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c26023 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {4, 5, 7} → False := by
  intro a294 a2 a102
  have hc := h.complementary {2, 6, 8, 9} {0, 1, 3} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a2 a102

theorem c26031 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 3, 4} → T {1, 5, 7} → False := by
  intro a294 a16 a56
  have hc := h.complementary {2, 6, 8, 9} {0, 3, 4} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a16 a56

theorem c26038 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 5} → False := by
  intro a294 n24 n45
  have hc := h.complementary {2, 6, 8, 9} {0, 4, 7} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 5} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n45)

theorem c26039 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 4, 7} → T {1, 3, 5} → False := by
  intro a294 a24 a45
  have hc := h.complementary {2, 6, 8, 9} {0, 4, 7} a294 (by decide) (by decide)
  have he : ( {2, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 5} := by decide
  rw [he] at hc
  exact hc.mp a24 a45

theorem c26045 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a294 a2 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {0, 1} {3, 4, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c26047 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a294 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {0, 1} {3, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

end BorsukNine.FiniteObstruction

end OAI
