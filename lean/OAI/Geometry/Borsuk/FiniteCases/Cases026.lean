import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c3411 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a132 a72 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 8} {4, 6} {2, 5, 7} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c3422 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a132 n73 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 8} {4, 7} {2, 6, 9} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c3483 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {6, 7, 8} → False := by
  intro a133 a71 a117
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 5} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a71 a117

theorem c3484 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a133 n72 n114
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n72 (hc.mpr n114)

theorem c3485 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 6} → T {5, 7, 8} → False := by
  intro a133 a72 a114
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a72 a114

theorem c3488 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 4, 8} → ¬ T {5, 6, 7} → False := by
  intro a133 n74 n111
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n74 (hc.mpr n111)

theorem c3489 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {5, 6, 7} → False := by
  intro a133 a74 a111
  have hc := h.complementary {0, 1, 3, 9} {2, 4, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a74 a111

theorem c3490 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 5, 6} → ¬ T {4, 7, 8} → False := by
  intro a133 n76 n108
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n76 (hc.mpr n108)

theorem c3491 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 5, 6} → T {4, 7, 8} → False := by
  intro a133 a76 a108
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 6} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a76 a108

theorem c3492 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 5, 7} → ¬ T {4, 6, 8} → False := by
  intro a133 n77 n106
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n77 (hc.mpr n106)

theorem c3493 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 5, 7} → T {4, 6, 8} → False := by
  intro a133 a77 a106
  have hc := h.complementary {0, 1, 3, 9} {2, 5, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a77 a106

theorem c3496 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → ¬ T {2, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a133 n80 n103
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n80 (hc.mpr n103)

theorem c3497 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 6, 7} → T {4, 5, 8} → False := by
  intro a133 a80 a103
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 7} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a80 a103

theorem c3499 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 6, 8} → T {4, 5, 7} → False := by
  intro a133 a81 a102
  have hc := h.complementary {0, 1, 3, 9} {2, 6, 8} a133 (by decide) (by decide)
  have he : ( {0, 1, 3, 9} : Finset Labels)ᶜ \ {2, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a81 a102

theorem c3503 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 4, 6} → T {2, 4, 7} → False := by
  intro a133 a71 a72 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 4} {5, 6, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c3511 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a133 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 6, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c3513 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a133 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 6, 8} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c3515 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 5} → T {2, 5, 7} → T {2, 5, 8} → False := by
  intro a133 a71 a77 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {2, 5} {4, 7, 8} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c3567 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {4, 5, 8} → T {4, 6, 8} → False := by
  intro a133 a74 a103 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {4, 8} {2, 5, 6} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)

theorem c3569 (h : TenSystem T Q) :
    Q {0, 1, 3, 9} → T {2, 4, 8} → T {4, 5, 8} → T {4, 7, 8} → False := by
  intro a133 a74 a103 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 9} {4, 8} {2, 5, 7} a133 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c3623 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → T {2, 3, 6} → T {7, 8, 9} → False := by
  intro a134 a67 a120
  have hc := h.complementary {0, 1, 4, 5} {2, 3, 6} a134 (by decide) (by decide)
  have he : ( {0, 1, 4, 5} : Finset Labels)ᶜ \ {2, 3, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a67 a120

theorem c3735 (h : TenSystem T Q) :
    Q {0, 1, 4, 5} → T {2, 6, 9} → T {6, 7, 9} → T {6, 8, 9} → False := by
  intro a134 a82 a118 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 5} {6, 9} {2, 7, 8} a134 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c3764 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {2, 3, 7} → ¬ T {5, 8, 9} → False := by
  intro a135 n68 n116
  have hc := h.complementary {0, 1, 4, 6} {2, 3, 7} a135 (by decide) (by decide)
  have he : ( {0, 1, 4, 6} : Finset Labels)ᶜ \ {2, 3, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n68 (hc.mpr n116)

theorem c3779 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → T {2, 7, 9} → T {3, 5, 8} → False := by
  intro a135 a84 a93
  have hc := h.complementary {0, 1, 4, 6} {2, 7, 9} a135 (by decide) (by decide)
  have he : ( {0, 1, 4, 6} : Finset Labels)ᶜ \ {2, 7, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a84 a93

theorem c3817 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → T {2, 3, 9} → T {2, 5, 9} → T {2, 8, 9} → False := by
  intro a135 a70 a79 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 6} {2, 9} {3, 5, 8} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c3846 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {2, 3, 9} → ¬ T {3, 5, 9} → ¬ T {3, 7, 9} → False := by
  intro a135 n70 n94 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 6} {3, 9} {2, 5, 7} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c3850 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → ¬ T {2, 3, 9} → ¬ T {3, 7, 9} → ¬ T {3, 8, 9} → False := by
  intro a135 n70 n99 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 6} {3, 9} {2, 7, 8} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c3865 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → T {2, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a135 a78 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 6} {5, 8} {2, 3, 9} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c3901 (h : TenSystem T Q) :
    Q {0, 1, 4, 6} → T {3, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a135 a100 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 6} {8, 9} {3, 5, 7} a135 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c3902 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {2, 3, 5} → ¬ T {6, 8, 9} → False := by
  intro a136 n66 n119
  have hc := h.complementary {0, 1, 4, 7} {2, 3, 5} a136 (by decide) (by decide)
  have he : ( {0, 1, 4, 7} : Finset Labels)ᶜ \ {2, 3, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n66 (hc.mpr n119)

theorem c3904 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {2, 3, 6} → ¬ T {5, 8, 9} → False := by
  intro a136 n67 n116
  have hc := h.complementary {0, 1, 4, 7} {2, 3, 6} a136 (by decide) (by decide)
  have he : ( {0, 1, 4, 7} : Finset Labels)ᶜ \ {2, 3, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n67 (hc.mpr n116)

theorem c3909 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 3, 9} → T {5, 6, 8} → False := by
  intro a136 a70 a112
  have hc := h.complementary {0, 1, 4, 7} {2, 3, 9} a136 (by decide) (by decide)
  have he : ( {0, 1, 4, 7} : Finset Labels)ᶜ \ {2, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a70 a112

theorem c3957 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 3, 9} → T {2, 5, 9} → T {2, 8, 9} → False := by
  intro a136 a70 a79 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {2, 9} {3, 5, 8} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c3984 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {3, 5, 8} → ¬ T {3, 6, 8} → ¬ T {3, 8, 9} → False := by
  intro a136 n93 n96 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 7} {3, 8} {5, 6, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 8} = {3, 5, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 8} = {3, 6, 8} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 8} = {3, 8, 9} by decide)) ht)

theorem c3989 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 3, 9} → T {3, 5, 9} → T {3, 8, 9} → False := by
  intro a136 a70 a94 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {3, 9} {2, 5, 8} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c3997 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 5, 6} → T {3, 5, 6} → T {5, 6, 9} → False := by
  intro a136 a76 a91 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {5, 6} {2, 3, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c4004 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a136 n78 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 7} {5, 8} {2, 3, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c4005 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {2, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a136 a78 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {5, 8} {2, 3, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c4008 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a136 n93 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 7} {5, 8} {3, 6, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c4024 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → ¬ T {3, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a136 n96 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 7} {6, 8} {3, 5, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c4025 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {3, 6, 8} → T {5, 6, 8} → T {6, 8, 9} → False := by
  intro a136 a96 a112 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {6, 8} {3, 5, 9} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) a96)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c4041 (h : TenSystem T Q) :
    Q {0, 1, 4, 7} → T {3, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a136 a100 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 7} {8, 9} {3, 5, 6} a136 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c4045 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 3, 6} → T {5, 7, 9} → False := by
  intro a137 a67 a115
  have hc := h.complementary {0, 1, 4, 8} {2, 3, 6} a137 (by decide) (by decide)
  have he : ( {0, 1, 4, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a67 a115

theorem c4048 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → ¬ T {2, 3, 9} → ¬ T {5, 6, 7} → False := by
  intro a137 n70 n111
  have hc := h.complementary {0, 1, 4, 8} {2, 3, 9} a137 (by decide) (by decide)
  have he : ( {0, 1, 4, 8} : Finset Labels)ᶜ \ {2, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n70 (hc.mpr n111)

theorem c4139 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a137 a76 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 6} {2, 7, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c4141 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {3, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a137 a91 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 6} {3, 7, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

end BorsukNine.FiniteObstruction

end OAI
