import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c17587 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a233 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 7} {0, 6, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c17594 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 4, 9} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → False := by
  intro a233 n26 n107 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 9} {0, 6, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n26 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c17596 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {2, 4, 9} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → False := by
  intro a233 n75 n107 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 9} {2, 6, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n75 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c17602 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a233 n31 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {6, 7} {0, 4, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c17603 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a233 a31 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {6, 7} {0, 4, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c17611 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a233 a33 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {6, 9} {0, 4, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c17612 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {2, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a233 n82 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {6, 9} {2, 4, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c17619 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a233 a35 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {7, 9} {0, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c17621 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {2, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a233 a84 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {7, 9} {2, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c17622 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 4} → ¬ T {6, 7, 8} → False := by
  intro a234 n10 n117
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 4} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n117)

theorem c17624 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 6} → ¬ T {4, 7, 8} → False := by
  intro a234 n12 n108
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 6} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n108)

theorem c17625 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 6} → T {4, 7, 8} → False := by
  intro a234 a12 a108
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 6} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a108

theorem c17626 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 7} → ¬ T {4, 6, 8} → False := by
  intro a234 n13 n106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n106)

theorem c17627 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 7} → T {4, 6, 8} → False := by
  intro a234 a13 a106
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a106

theorem c17628 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 2, 8} → ¬ T {4, 6, 7} → False := by
  intro a234 n14 n105
  have hc := h.complementary {1, 3, 5, 9} {0, 2, 8} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n105)

theorem c17634 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 6, 7} → False := by
  intro a234 n25 n80
  have hc := h.complementary {1, 3, 5, 9} {0, 4, 8} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n80)

theorem c17636 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 6, 7} → ¬ T {2, 4, 8} → False := by
  intro a234 n31 n74
  have hc := h.complementary {1, 3, 5, 9} {0, 6, 7} a234 (by decide) (by decide)
  have he : ( {1, 3, 5, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n74)

theorem c17645 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a234 a10 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 2} {4, 6, 8} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17651 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a234 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 4} {2, 6, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c17675 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 2, 8} → T {0, 4, 8} → T {0, 6, 8} → False := by
  intro a234 a14 a25 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {0, 8} {2, 4, 6} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c17730 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 6, 8} → False := by
  intro a234 n25 n74 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 9} {4, 8} {0, 2, 6} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)

theorem c17732 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 7, 8} → False := by
  intro a234 n25 n74 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 9} {4, 8} {0, 2, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)

theorem c17735 (h : TenSystem T Q) :
    Q {1, 3, 5, 9} → T {0, 4, 8} → T {4, 6, 8} → T {4, 7, 8} → False := by
  intro a234 a25 a106 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 9} {4, 8} {0, 6, 7} a234 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c17762 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 4} → ¬ T {5, 8, 9} → False := by
  intro a235 n10 n116
  have hc := h.complementary {1, 3, 6, 7} {0, 2, 4} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n116)

theorem c17763 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 2, 4} → T {5, 8, 9} → False := by
  intro a235 a10 a116
  have hc := h.complementary {1, 3, 6, 7} {0, 2, 4} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a116

theorem c17768 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 9} → ¬ T {4, 5, 8} → False := by
  intro a235 n15 n103
  have hc := h.complementary {1, 3, 6, 7} {0, 2, 9} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n103)

theorem c17769 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 2, 9} → T {4, 5, 8} → False := by
  intro a235 a15 a103
  have hc := h.complementary {1, 3, 6, 7} {0, 2, 9} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a103

theorem c17774 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 4, 9} → ¬ T {2, 5, 8} → False := by
  intro a235 n26 n78
  have hc := h.complementary {1, 3, 6, 7} {0, 4, 9} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 4, 9} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n78)

theorem c17777 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 8} → T {2, 4, 9} → False := by
  intro a235 a29 a75
  have hc := h.complementary {1, 3, 6, 7} {0, 5, 8} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a75

theorem c17779 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 9} → T {2, 4, 8} → False := by
  intro a235 a30 a74
  have hc := h.complementary {1, 3, 6, 7} {0, 5, 9} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 5, 9} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a30 a74

theorem c17781 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 8, 9} → T {2, 4, 5} → False := by
  intro a235 a36 a71
  have hc := h.complementary {1, 3, 6, 7} {0, 8, 9} a235 (by decide) (by decide)
  have he : ( {1, 3, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a36 a71

theorem c17790 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 8} → False := by
  intro a235 n10 n22 n25
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 7} {0, 4} {2, 5, 8} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n25 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 4} = {0, 4, 8} by decide)) ht)

theorem c17817 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 2, 9} → T {0, 4, 9} → T {0, 8, 9} → False := by
  intro a235 a15 a26 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {0, 9} {2, 4, 8} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c17824 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 4} → ¬ T {2, 4, 5} → ¬ T {2, 4, 9} → False := by
  intro a235 n10 n71 n75
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 7} {2, 4} {0, 5, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) ht)

theorem c17826 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {0, 2, 4} → ¬ T {2, 4, 8} → ¬ T {2, 4, 9} → False := by
  intro a235 n10 n74 n75
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 7} {2, 4} {0, 8, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 4} = {2, 4, 8} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) ht)

theorem c17860 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a235 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 7} {4, 5} {2, 8, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c17879 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 8} → T {2, 5, 8} → T {4, 5, 8} → False := by
  intro a235 a29 a78 a103
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {0, 2, 4} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)

theorem c17881 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a235 a29 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {0, 2, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c17883 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a235 a29 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {0, 4, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c17885 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a235 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {5, 8} {2, 4, 9} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c17899 (h : TenSystem T Q) :
    Q {1, 3, 6, 7} → T {0, 8, 9} → T {4, 8, 9} → T {5, 8, 9} → False := by
  intro a235 a36 a110 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 7} {8, 9} {0, 4, 5} a235 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c17902 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {0, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a236 n10 n115
  have hc := h.complementary {1, 3, 6, 8} {0, 2, 4} a236 (by decide) (by decide)
  have he : ( {1, 3, 6, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n115)

theorem c17908 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → ¬ T {0, 2, 9} → ¬ T {4, 5, 7} → False := by
  intro a236 n15 n102
  have hc := h.complementary {1, 3, 6, 8} {0, 2, 9} a236 (by decide) (by decide)
  have he : ( {1, 3, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n102)

theorem c17957 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a236 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {0, 9} {2, 4, 7} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c18005 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a236 a24 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {4, 7} {0, 2, 9} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c18007 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 9} → False := by
  intro a236 a24 a102 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {4, 7} {0, 5, 9} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

end BorsukNine.FiniteObstruction

end OAI
