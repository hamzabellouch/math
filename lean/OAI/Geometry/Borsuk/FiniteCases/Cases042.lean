import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c12596 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 4, 6} → ¬ T {2, 3, 9} → False := by
  intro a198 n51 n70
  have hc := h.complementary {0, 5, 7, 8} {1, 4, 6} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n70)

theorem c12597 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 4, 6} → T {2, 3, 9} → False := by
  intro a198 a51 a70
  have hc := h.complementary {0, 5, 7, 8} {1, 4, 6} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a70

theorem c12605 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a198 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 2} {3, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12607 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a198 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 2} {3, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12613 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a198 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 3} {2, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12615 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a198 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 3} {2, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12616 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 4} → ¬ T {1, 3, 6} → ¬ T {1, 3, 9} → False := by
  intro a198 n44 n46 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {1, 3} {4, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c12634 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 4, 9} → False := by
  intro a198 n43 n49 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {1, 9} {2, 3, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) ht)

theorem c12635 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 4, 9} → False := by
  intro a198 a43 a49 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {1, 9} {2, 3, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)

theorem c12636 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 6, 9} → False := by
  intro a198 n43 n49 n61
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {1, 9} {2, 3, 6} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n61 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) ht)

theorem c12645 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a198 a37 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 3} {1, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12647 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a198 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 3} {1, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12657 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {2, 3, 4} → T {2, 4, 6} → T {2, 4, 9} → False := by
  intro a198 a65 a72 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 4} {3, 6, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) a75)

theorem c12663 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 6} → T {2, 4, 6} → T {2, 6, 9} → False := by
  intro a198 a40 a72 a82
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {2, 6} {1, 4, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) a82)

theorem c12682 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 4, 6} → False := by
  intro a198 n46 n67 n87
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {3, 6} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)

theorem c12684 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 9} → False := by
  intro a198 n46 n67 n97
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {3, 6} {1, 2, 9} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) ht)

theorem c12690 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a198 n49 n70 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {3, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c12691 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 4, 9} → False := by
  intro a198 a49 a70 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {3, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)

theorem c12695 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 9} → T {3, 4, 9} → T {3, 6, 9} → False := by
  intro a198 a49 a90 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {3, 9} {1, 4, 6} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c12699 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 4, 6} → T {2, 4, 6} → T {3, 4, 6} → False := by
  intro a198 a51 a72 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {4, 6} {1, 2, 3} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c12707 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 4, 9} → T {2, 4, 9} → T {3, 4, 9} → False := by
  intro a198 a54 a75 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 8} {4, 9} {1, 2, 3} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)

theorem c12710 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 4, 9} → ¬ T {3, 4, 9} → ¬ T {4, 6, 9} → False := by
  intro a198 n54 n90 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {4, 9} {1, 3, 6} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n54 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)

theorem c12716 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 6, 9} → ¬ T {2, 6, 9} → ¬ T {4, 6, 9} → False := by
  intro a198 n61 n82 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 7, 8} {6, 9} {1, 2, 4} a198 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n61 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)

theorem c12723 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 2, 3} → T {4, 6, 8} → False := by
  intro a199 a37 a106
  have hc := h.complementary {0, 5, 7, 9} {1, 2, 3} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a106

theorem c12726 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ T {1, 2, 6} → ¬ T {3, 4, 8} → False := by
  intro a199 n40 n89
  have hc := h.complementary {0, 5, 7, 9} {1, 2, 6} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n89)

theorem c12735 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 3, 8} → T {2, 4, 6} → False := by
  intro a199 a48 a72
  have hc := h.complementary {0, 5, 7, 9} {1, 3, 8} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a48 a72

theorem c12736 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → ¬ T {1, 4, 6} → ¬ T {2, 3, 8} → False := by
  intro a199 n51 n69
  have hc := h.complementary {0, 5, 7, 9} {1, 4, 6} a199 (by decide) (by decide)
  have he : ( {0, 5, 7, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 3, 8} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n69)

theorem c12751 (h : TenSystem T Q) :
    Q {0, 5, 7, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a199 a37 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 7, 9} {1, 3} {2, 4, 6} a199 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c12863 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {4, 6, 7} → False := by
  intro a200 a37 a105
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 3} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a105

theorem c12864 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {3, 6, 7} → False := by
  intro a200 n38 n95
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 4} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n95)

theorem c12866 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 6} → ¬ T {3, 4, 7} → False := by
  intro a200 n40 n88
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 6} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n88)

theorem c12867 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {3, 4, 7} → False := by
  intro a200 a40 a88
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 6} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a40 a88

theorem c12868 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 7} → ¬ T {3, 4, 6} → False := by
  intro a200 n41 n87
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {3, 4, 6} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n87)

theorem c12869 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 7} → T {3, 4, 6} → False := by
  intro a200 a41 a87
  have hc := h.complementary {0, 5, 8, 9} {1, 2, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a41 a87

theorem c12871 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 4} → T {2, 6, 7} → False := by
  intro a200 a44 a80
  have hc := h.complementary {0, 5, 8, 9} {1, 3, 4} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a44 a80

theorem c12872 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 3, 6} → ¬ T {2, 4, 7} → False := by
  intro a200 n46 n73
  have hc := h.complementary {0, 5, 8, 9} {1, 3, 6} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n46 (hc.mpr n73)

theorem c12874 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 3, 7} → ¬ T {2, 4, 6} → False := by
  intro a200 n47 n72
  have hc := h.complementary {0, 5, 8, 9} {1, 3, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n72)

theorem c12875 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {2, 4, 6} → False := by
  intro a200 a47 a72
  have hc := h.complementary {0, 5, 8, 9} {1, 3, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a47 a72

theorem c12877 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 4, 6} → T {2, 3, 7} → False := by
  intro a200 a51 a68
  have hc := h.complementary {0, 5, 8, 9} {1, 4, 6} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a51 a68

theorem c12878 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 4, 7} → ¬ T {2, 3, 6} → False := by
  intro a200 n52 n67
  have hc := h.complementary {0, 5, 8, 9} {1, 4, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n67)

theorem c12881 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 6, 7} → T {2, 3, 4} → False := by
  intro a200 a59 a65
  have hc := h.complementary {0, 5, 8, 9} {1, 6, 7} a200 (by decide) (by decide)
  have he : ( {0, 5, 8, 9} : Finset Labels)ᶜ \ {1, 6, 7} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a59 a65

theorem c12883 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a200 a37 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 2} {3, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c12885 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 7} → False := by
  intro a200 a37 a38 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 2} {3, 4, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c12887 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a200 a37 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 2} {3, 6, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c12888 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → False := by
  intro a200 n38 n40 n41
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {1, 2} {4, 6, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)

theorem c12891 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 6} → False := by
  intro a200 a37 a44 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 3} {2, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

end BorsukNine.FiniteObstruction

end OAI
