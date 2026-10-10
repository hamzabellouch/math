import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28527 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a311 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {4, 7} {0, 1, 2} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

theorem c28528 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a311 n24 n52 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {4, 7} {0, 1, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c28530 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a311 n24 n73 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {4, 7} {0, 2, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c28535 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {2, 6, 7} → False := by
  intro a311 a31 a59 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {6, 7} {0, 1, 2} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)

theorem c28543 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {4, 5, 9} → False := by
  intro a312 a1 a104
  have hc := h.complementary {3, 6, 7, 8} {0, 1, 2} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a104

theorem c28544 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 1, 4} → ¬ T {2, 5, 9} → False := by
  intro a312 n3 n79
  have hc := h.complementary {3, 6, 7, 8} {0, 1, 4} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n79)

theorem c28550 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {1, 5, 9} → False := by
  intro a312 n10 n58
  have hc := h.complementary {3, 6, 7, 8} {0, 2, 4} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n58)

theorem c28555 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 2, 9} → T {1, 4, 5} → False := by
  intro a312 a15 a50
  have hc := h.complementary {3, 6, 7, 8} {0, 2, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a15 a50

theorem c28558 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 4, 9} → ¬ T {1, 2, 5} → False := by
  intro a312 n26 n39
  have hc := h.complementary {3, 6, 7, 8} {0, 4, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n39)

theorem c28560 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 5, 9} → ¬ T {1, 2, 4} → False := by
  intro a312 n30 n38
  have hc := h.complementary {3, 6, 7, 8} {0, 5, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n30 (hc.mpr n38)

theorem c28561 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 5, 9} → T {1, 2, 4} → False := by
  intro a312 a30 a38
  have hc := h.complementary {3, 6, 7, 8} {0, 5, 9} a312 (by decide) (by decide)
  have he : ( {3, 6, 7, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a30 a38

theorem c28603 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 5} → False := by
  intro a312 a1 a38 a39
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 4, 5} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)

theorem c28605 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a312 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 4, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28607 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a312 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 2} {0, 5, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28618 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 1, 5} → ¬ T {1, 2, 5} → ¬ T {1, 4, 5} → False := by
  intro a312 n4 n39 n50
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {1, 5} {0, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) ht)

theorem c28619 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 1, 5} → T {1, 2, 5} → T {1, 4, 5} → False := by
  intro a312 a4 a39 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {1, 5} {0, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)

theorem c28655 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 2, 9} → T {2, 4, 9} → T {2, 5, 9} → False := by
  intro a312 a15 a75 a79
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {2, 9} {0, 4, 5} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)

theorem c28662 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 9} → False := by
  intro a312 n22 n71 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {4, 5} {0, 2, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c28664 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {1, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 9} → False := by
  intro a312 n50 n71 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {4, 5} {1, 2, 9} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c28667 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → T {0, 4, 9} → T {1, 4, 9} → T {2, 4, 9} → False := by
  intro a312 a26 a54 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 8} {4, 9} {0, 1, 2} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)

theorem c28678 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {0, 5, 9} → ¬ T {2, 5, 9} → ¬ T {4, 5, 9} → False := by
  intro a312 n30 n79 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {5, 9} {0, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n30 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) ht)
  · exact n79 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 9} = {2, 5, 9} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)

theorem c28680 (h : TenSystem T Q) :
    Q {3, 6, 7, 8} → ¬ T {1, 5, 9} → ¬ T {2, 5, 9} → ¬ T {4, 5, 9} → False := by
  intro a312 n58 n79 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 8} {5, 9} {1, 2, 4} a312 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n58 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) ht)
  · exact n79 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 9} = {2, 5, 9} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)

theorem c28683 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {4, 5, 8} → False := by
  intro a313 a1 a103
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 2} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a103

theorem c28685 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 4} → T {2, 5, 8} → False := by
  intro a313 a3 a78
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 4} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a3 a78

theorem c28686 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 8} → False := by
  intro a313 n4 n74
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n74)

theorem c28688 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {2, 4, 5} → False := by
  intro a313 n7 n71
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n71)

theorem c28689 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 8} → T {2, 4, 5} → False := by
  intro a313 a7 a71
  have hc := h.complementary {3, 6, 7, 9} {0, 1, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a7 a71

theorem c28690 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {1, 5, 8} → False := by
  intro a313 n10 n57
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 4} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n57)

theorem c28691 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 2, 4} → T {1, 5, 8} → False := by
  intro a313 a10 a57
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 4} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a57

theorem c28694 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 2, 8} → ¬ T {1, 4, 5} → False := by
  intro a313 n14 n50
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 4, 5} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n50)

theorem c28695 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 2, 8} → T {1, 4, 5} → False := by
  intro a313 a14 a50
  have hc := h.complementary {3, 6, 7, 9} {0, 2, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a14 a50

theorem c28696 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 8} → False := by
  intro a313 n22 n42
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n42)

theorem c28697 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 4, 5} → T {1, 2, 8} → False := by
  intro a313 a22 a42
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 5} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 8} := by decide
  rw [he] at hc
  exact hc.mp a22 a42

theorem c28698 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 8} → ¬ T {1, 2, 5} → False := by
  intro a313 n25 n39
  have hc := h.complementary {3, 6, 7, 9} {0, 4, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n39)

theorem c28700 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 4} → False := by
  intro a313 n29 n38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n38)

theorem c28701 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 5, 8} → T {1, 2, 4} → False := by
  intro a313 a29 a38
  have hc := h.complementary {3, 6, 7, 9} {0, 5, 8} a313 (by decide) (by decide)
  have he : ( {3, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a29 a38

theorem c28705 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 8} → False := by
  intro a313 a1 a3 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 1} {2, 4, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c28707 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 1, 5} → T {0, 1, 8} → False := by
  intro a313 a1 a4 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 1} {2, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c28715 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a313 a1 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {0, 2} {1, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c28738 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {0, 4, 8} → ¬ T {0, 5, 8} → False := by
  intro a313 n7 n25 n29
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {0, 8} {1, 4, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) ht)
  · exact n25 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) ht)
  · exact n29 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) ht)

theorem c28743 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 5} → False := by
  intro a313 a1 a38 a39
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 4, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)

theorem c28745 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 8} → False := by
  intro a313 a1 a38 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 4, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28747 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a313 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 2} {0, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28748 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {1, 2, 4} → ¬ T {1, 2, 5} → ¬ T {1, 2, 8} → False := by
  intro a313 n38 n39 n42
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 2} {4, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) ht)

theorem c28753 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 4} → T {1, 2, 4} → T {1, 4, 8} → False := by
  intro a313 a3 a38 a53
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 4} {0, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 4} = {1, 4, 8} by decide)) a53)

theorem c28759 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 1, 5} → T {1, 2, 5} → T {1, 4, 5} → False := by
  intro a313 a4 a39 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {1, 5} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)

theorem c28766 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 4, 8} → False := by
  intro a313 n7 n42 n53
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 8} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n53 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
