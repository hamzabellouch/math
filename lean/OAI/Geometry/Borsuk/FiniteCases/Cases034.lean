import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c8513 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a168 a93 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {5, 8} {3, 4, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c8520 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a168 n96 n106 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {6, 8} {3, 4, 5} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)

theorem c8527 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 3, 6} → T {4, 5, 7} → False := by
  intro a169 a46 a102
  have hc := h.complementary {0, 2, 8, 9} {1, 3, 6} a169 (by decide) (by decide)
  have he : ( {0, 2, 8, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a46 a102

theorem c8528 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 3, 7} → ¬ T {4, 5, 6} → False := by
  intro a169 n47 n101
  have hc := h.complementary {0, 2, 8, 9} {1, 3, 7} a169 (by decide) (by decide)
  have he : ( {0, 2, 8, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n101)

theorem c8531 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 5} → T {3, 6, 7} → False := by
  intro a169 a50 a95
  have hc := h.complementary {0, 2, 8, 9} {1, 4, 5} a169 (by decide) (by decide)
  have he : ( {0, 2, 8, 9} : Finset Labels)ᶜ \ {1, 4, 5} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a50 a95

theorem c8568 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a169 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {1, 6} {3, 4, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c8615 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a169 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 5} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8625 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a169 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 6} {1, 3, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c8626 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a169 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {4, 6} {1, 5, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c8627 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a169 a51 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 6} {1, 5, 7} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c8633 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → T {1, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a169 a52 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 8, 9} {4, 7} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c8648 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a169 n56 n92 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {5, 7} {1, 3, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c8652 (h : TenSystem T Q) :
    Q {0, 2, 8, 9} → ¬ T {3, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a169 n92 n102 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 8, 9} {5, 7} {3, 4, 6} a169 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c8662 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 6} → ¬ T {7, 8, 9} → False := by
  intro a170 n40 n120
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 6} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n120)

theorem c8664 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 7} → ¬ T {6, 8, 9} → False := by
  intro a170 n41 n119
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 7} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n119)

theorem c8666 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → ¬ T {1, 2, 8} → ¬ T {6, 7, 9} → False := by
  intro a170 n42 n118
  have hc := h.complementary {0, 3, 4, 5} {1, 2, 8} a170 (by decide) (by decide)
  have he : ( {0, 3, 4, 5} : Finset Labels)ᶜ \ {1, 2, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n118)

theorem c8789 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → T {1, 7, 9} → T {2, 7, 9} → T {7, 8, 9} → False := by
  intro a170 a63 a84 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 5} {7, 9} {1, 2, 8} a170 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c8799 (h : TenSystem T Q) :
    Q {0, 3, 4, 5} → T {1, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a170 a64 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 5} {8, 9} {1, 6, 7} a170 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c8804 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → ¬ T {1, 2, 7} → ¬ T {5, 8, 9} → False := by
  intro a171 n41 n116
  have hc := h.complementary {0, 3, 4, 6} {1, 2, 7} a171 (by decide) (by decide)
  have he : ( {0, 3, 4, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n116)

theorem c8805 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 2, 7} → T {5, 8, 9} → False := by
  intro a171 a41 a116
  have hc := h.complementary {0, 3, 4, 6} {1, 2, 7} a171 (by decide) (by decide)
  have he : ( {0, 3, 4, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a116

theorem c8813 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 8} → T {2, 7, 9} → False := by
  intro a171 a57 a84
  have hc := h.complementary {0, 3, 4, 6} {1, 5, 8} a171 (by decide) (by decide)
  have he : ( {0, 3, 4, 6} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a84

theorem c8857 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 2, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a171 a43 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {1, 9} {2, 5, 8} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c8889 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 2, 9} → T {2, 5, 9} → T {2, 8, 9} → False := by
  intro a171 a43 a79 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {2, 9} {1, 5, 8} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c8903 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 8} → T {2, 5, 8} → T {5, 7, 8} → False := by
  intro a171 a57 a78 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 8} {1, 2, 7} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c8905 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a171 a57 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 8} {1, 2, 9} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c8915 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a171 a58 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {5, 9} {1, 7, 8} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c8939 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a171 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 6} {8, 9} {1, 5, 7} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c8940 (h : TenSystem T Q) :
    Q {0, 3, 4, 6} → ¬ T {2, 8, 9} → ¬ T {5, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a171 n85 n116 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 6} {8, 9} {2, 5, 7} a171 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n85 (Eq.mp (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c8942 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 5} → ¬ T {6, 8, 9} → False := by
  intro a172 n39 n119
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 5} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n119)

theorem c8944 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 6} → ¬ T {5, 8, 9} → False := by
  intro a172 n40 n116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n116)

theorem c8945 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 2, 6} → T {5, 8, 9} → False := by
  intro a172 a40 a116
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 6} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a116

theorem c8948 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 2, 9} → ¬ T {5, 6, 8} → False := by
  intro a172 n43 n112
  have hc := h.complementary {0, 3, 4, 7} {1, 2, 9} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n112)

theorem c8952 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → ¬ T {1, 5, 8} → ¬ T {2, 6, 9} → False := by
  intro a172 n57 n82
  have hc := h.complementary {0, 3, 4, 7} {1, 5, 8} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 6, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n82)

theorem c8953 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {2, 6, 9} → False := by
  intro a172 a57 a82
  have hc := h.complementary {0, 3, 4, 7} {1, 5, 8} a172 (by decide) (by decide)
  have he : ( {0, 3, 4, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a82

theorem c9037 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 6} → T {2, 5, 6} → T {5, 6, 9} → False := by
  intro a172 a55 a76 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 6} {1, 2, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c9045 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a172 a57 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 8} {1, 2, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c9047 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a172 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {5, 8} {1, 6, 9} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c9071 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 6, 9} → T {5, 6, 9} → T {6, 8, 9} → False := by
  intro a172 a61 a113 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {6, 9} {1, 5, 8} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c9073 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {2, 6, 9} → T {5, 6, 9} → T {6, 8, 9} → False := by
  intro a172 a82 a113 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {6, 9} {2, 5, 8} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c9079 (h : TenSystem T Q) :
    Q {0, 3, 4, 7} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a172 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 7} {8, 9} {1, 5, 6} a172 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c9082 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 5} → ¬ T {6, 7, 9} → False := by
  intro a173 n39 n118
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 5} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n118)

theorem c9084 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 6} → ¬ T {5, 7, 9} → False := by
  intro a173 n40 n115
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 6} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n115)

theorem c9086 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → ¬ T {1, 2, 7} → ¬ T {5, 6, 9} → False := by
  intro a173 n41 n113
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 7} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n113)

theorem c9087 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 7} → T {5, 6, 9} → False := by
  intro a173 a41 a113
  have hc := h.complementary {0, 3, 4, 8} {1, 2, 7} a173 (by decide) (by decide)
  have he : ( {0, 3, 4, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a113

theorem c9115 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a173 a39 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {1, 5} {2, 7, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c9151 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a173 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {2, 6} {1, 5, 7} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

end BorsukNine.FiniteObstruction

end OAI
