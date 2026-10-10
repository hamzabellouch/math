import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18472 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 6} → ¬ T {2, 5, 7} → False := by
  intro a240 n23 n77
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n77)

theorem c18474 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 5, 6} → False := by
  intro a240 n24 n76
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n76)

theorem c18476 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 4, 7} → False := by
  intro a240 n27 n73
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n73)

theorem c18477 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 5, 6} → T {2, 4, 7} → False := by
  intro a240 a27 a73
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a27 a73

theorem c18478 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 5, 7} → ¬ T {2, 4, 6} → False := by
  intro a240 n28 n72
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n72)

theorem c18479 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 5, 7} → T {2, 4, 6} → False := by
  intro a240 a28 a72
  have hc := h.complementary {1, 3, 8, 9} {0, 5, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a28 a72

theorem c18481 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 6, 7} → T {2, 4, 5} → False := by
  intro a240 a31 a71
  have hc := h.complementary {1, 3, 8, 9} {0, 6, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a31 a71

theorem c18485 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a240 a10 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {4, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18487 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a240 a10 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {4, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18488 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a240 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c18489 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a240 a11 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {0, 2} {5, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18500 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a240 n11 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {0, 5} {2, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c18530 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {2, 4, 5} → ¬ T {2, 5, 6} → False := by
  intro a240 n11 n71 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 5} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) ht)

theorem c18531 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a240 a11 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c18533 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {2, 4, 5} → T {2, 5, 7} → False := by
  intro a240 a11 a71 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {0, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c18537 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a240 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 5} {4, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c18540 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a240 n12 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 6} {0, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c18548 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 7} → ¬ T {2, 4, 7} → ¬ T {2, 6, 7} → False := by
  intro a240 n13 n73 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {2, 7} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c18549 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {2, 4, 7} → T {2, 6, 7} → False := by
  intro a240 a13 a73 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 7} {0, 4, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c18551 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a240 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {2, 7} {0, 5, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c18554 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 6} → False := by
  intro a240 n22 n71 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 2, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)

theorem c18555 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a240 a22 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {0, 2, 6} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c18556 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 7} → False := by
  intro a240 n22 n71 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 2, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c18558 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → False := by
  intro a240 n22 n101 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 5} {0, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c18559 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a240 a22 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {0, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c18561 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {2, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a240 a71 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 5} {2, 6, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c18565 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a240 a23 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 6} {0, 2, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c18567 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a240 a23 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 8, 9} {4, 6} {0, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c18568 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {2, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a240 n72 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {4, 6} {2, 5, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c18584 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a240 n76 n101 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 8, 9} {5, 6} {2, 4, 7} a240 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c18603 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {7, 8, 9} → False := by
  intro a241 a9 a120
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 3} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a120

theorem c18604 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {3, 8, 9} → False := by
  intro a241 n13 n100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n100)

theorem c18605 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 7} → T {3, 8, 9} → False := by
  intro a241 a13 a100
  have hc := h.complementary {1, 4, 5, 6} {0, 2, 7} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a100

theorem c18612 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 3, 8} → ¬ T {2, 7, 9} → False := by
  intro a241 n20 n84
  have hc := h.complementary {1, 4, 5, 6} {0, 3, 8} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 7, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n84)

theorem c18614 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 3, 9} → ¬ T {2, 7, 8} → False := by
  intro a241 n21 n83
  have hc := h.complementary {1, 4, 5, 6} {0, 3, 9} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 7, 8} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n83)

theorem c18618 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → ¬ T {0, 7, 9} → ¬ T {2, 3, 8} → False := by
  intro a241 n35 n69
  have hc := h.complementary {1, 4, 5, 6} {0, 7, 9} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 3, 8} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n69)

theorem c18621 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 8, 9} → T {2, 3, 7} → False := by
  intro a241 a36 a68
  have hc := h.complementary {1, 4, 5, 6} {0, 8, 9} a241 (by decide) (by decide)
  have he : ( {1, 4, 5, 6} : Finset Labels)ᶜ \ {0, 8, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a36 a68

theorem c18631 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a241 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {0, 3} {2, 7, 8} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c18655 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a241 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {0, 9} {2, 3, 7} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c18667 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a241 a9 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {2, 3} {0, 8, 9} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c18715 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 3, 9} → T {3, 7, 9} → T {3, 8, 9} → False := by
  intro a241 a21 a99 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {3, 9} {0, 7, 8} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c18727 (h : TenSystem T Q) :
    Q {1, 4, 5, 6} → T {0, 7, 9} → T {2, 7, 9} → T {3, 7, 9} → False := by
  intro a241 a35 a84 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 6} {7, 9} {0, 2, 3} a241 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)

theorem c18743 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {6, 8, 9} → False := by
  intro a242 a9 a119
  have hc := h.complementary {1, 4, 5, 7} {0, 2, 3} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a119

theorem c18757 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 6, 8} → T {2, 3, 9} → False := by
  intro a242 a32 a70
  have hc := h.complementary {1, 4, 5, 7} {0, 6, 8} a242 (by decide) (by decide)
  have he : ( {1, 4, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a70

theorem c18765 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a242 a9 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {0, 2} {3, 6, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c18767 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 2, 3} → T {0, 2, 8} → T {0, 2, 9} → False := by
  intro a242 a9 a14 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {0, 2} {3, 8, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

end BorsukNine.FiniteObstruction

end OAI
