import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c2657 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 6, 7} → T {4, 5, 8} → False := by
  intro a127 a95 a103
  have hc := h.complementary {0, 1, 2, 9} {3, 6, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a95 a103

theorem c2661 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 7, 8} → T {4, 5, 6} → False := by
  intro a127 a98 a101
  have hc := h.complementary {0, 1, 2, 9} {3, 7, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a98 a101

theorem c2665 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a127 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {3, 4} {5, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c2673 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {3, 5, 6} → T {3, 5, 8} → False := by
  intro a127 a86 a91 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {3, 5} {4, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)

theorem c2678 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 4, 6} → ¬ T {3, 5, 6} → ¬ T {3, 6, 7} → False := by
  intro a127 n87 n91 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 9} {3, 6} {4, 5, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c2691 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 7} → T {3, 6, 7} → T {3, 7, 8} → False := by
  intro a127 a88 a95 a98
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {3, 7} {4, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 7} = {3, 7, 8} by decide)) a98)

theorem c2703 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a127 a86 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {4, 5} {3, 6, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c2747 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 7} → T {5, 6, 7} → T {5, 7, 8} → False := by
  intro a127 a92 a111 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {5, 7} {3, 6, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) a114)

theorem c2753 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a127 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {5, 8} {3, 4, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c2754 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a127 n93 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 9} {5, 8} {3, 6, 7} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c2763 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a127 a95 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 9} {6, 7} {3, 5, 8} a127 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c2789 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 9} → T {6, 7, 8} → False := by
  intro a128 a79 a117
  have hc := h.complementary {0, 1, 3, 4} {2, 5, 9} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a79 a117

theorem c2790 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → ¬ T {2, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a128 n80 n116
  have hc := h.complementary {0, 1, 3, 4} {2, 6, 7} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n80 (hc.mpr n116)

theorem c2791 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 6, 7} → T {5, 8, 9} → False := by
  intro a128 a80 a116
  have hc := h.complementary {0, 1, 3, 4} {2, 6, 7} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a80 a116

theorem c2795 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 6, 9} → T {5, 7, 8} → False := by
  intro a128 a82 a114
  have hc := h.complementary {0, 1, 3, 4} {2, 6, 9} a128 (by decide) (by decide)
  have he : ( {0, 1, 3, 4} : Finset Labels)ᶜ \ {2, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a82 a114

theorem c2811 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 6} → T {2, 6, 7} → T {2, 6, 8} → False := by
  intro a128 a76 a80 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 4} {2, 6} {5, 7, 8} a128 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

theorem c2861 (h : TenSystem T Q) :
    Q {0, 1, 3, 4} → T {2, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a128 a78 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 4} {5, 8} {2, 6, 9} a128 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c2927 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → T {2, 4, 8} → T {6, 7, 9} → False := by
  intro a129 a74 a118
  have hc := h.complementary {0, 1, 3, 5} {2, 4, 8} a129 (by decide) (by decide)
  have he : ( {0, 1, 3, 5} : Finset Labels)ᶜ \ {2, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a74 a118

theorem c2936 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {2, 7, 8} → ¬ T {4, 6, 9} → False := by
  intro a129 n83 n107
  have hc := h.complementary {0, 1, 3, 5} {2, 7, 8} a129 (by decide) (by decide)
  have he : ( {0, 1, 3, 5} : Finset Labels)ᶜ \ {2, 7, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n83 (hc.mpr n107)

theorem c2992 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a129 n73 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 5} {4, 7} {2, 6, 9} a129 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c3011 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → T {2, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a129 a75 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 5} {4, 9} {2, 7, 8} a129 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c3035 (h : TenSystem T Q) :
    Q {0, 1, 3, 5} → T {2, 6, 9} → T {6, 7, 9} → T {6, 8, 9} → False := by
  intro a129 a82 a118 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 5} {6, 9} {2, 7, 8} a129 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c3062 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a130 n71 n120
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 5} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n71 (hc.mpr n120)

theorem c3063 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 4, 5} → T {7, 8, 9} → False := by
  intro a130 a71 a120
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 5} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a120

theorem c3064 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a130 n73 n116
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 7} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n73 (hc.mpr n116)

theorem c3066 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 8} → ¬ T {5, 7, 9} → False := by
  intro a130 n74 n115
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n74 (hc.mpr n115)

theorem c3068 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 4, 9} → ¬ T {5, 7, 8} → False := by
  intro a130 n75 n114
  have hc := h.complementary {0, 1, 3, 6} {2, 4, 9} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 4, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n75 (hc.mpr n114)

theorem c3072 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a130 n78 n109
  have hc := h.complementary {0, 1, 3, 6} {2, 5, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n78 (hc.mpr n109)

theorem c3073 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 5, 8} → T {4, 7, 9} → False := by
  intro a130 a78 a109
  have hc := h.complementary {0, 1, 3, 6} {2, 5, 8} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a78 a109

theorem c3075 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 5, 9} → T {4, 7, 8} → False := by
  intro a130 a79 a108
  have hc := h.complementary {0, 1, 3, 6} {2, 5, 9} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 5, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a79 a108

theorem c3081 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → T {2, 8, 9} → T {4, 5, 7} → False := by
  intro a130 a85 a102
  have hc := h.complementary {0, 1, 3, 6} {2, 8, 9} a130 (by decide) (by decide)
  have he : ( {0, 1, 3, 6} : Finset Labels)ᶜ \ {2, 8, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a85 a102

theorem c3180 (h : TenSystem T Q) :
    Q {0, 1, 3, 6} → ¬ T {2, 7, 8} → ¬ T {4, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a130 n83 n108 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 6} {7, 8} {2, 4, 9} a130 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n83 (Eq.mp (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c3203 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 4, 5} → T {6, 8, 9} → False := by
  intro a131 a71 a119
  have hc := h.complementary {0, 1, 3, 7} {2, 4, 5} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a119

theorem c3205 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 4, 6} → T {5, 8, 9} → False := by
  intro a131 a72 a116
  have hc := h.complementary {0, 1, 3, 7} {2, 4, 6} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a116

theorem c3212 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ T {2, 5, 8} → ¬ T {4, 6, 9} → False := by
  intro a131 n78 n107
  have hc := h.complementary {0, 1, 3, 7} {2, 5, 8} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n78 (hc.mpr n107)

theorem c3219 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 6, 9} → T {4, 5, 8} → False := by
  intro a131 a82 a103
  have hc := h.complementary {0, 1, 3, 7} {2, 6, 9} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a82 a103

theorem c3221 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 8, 9} → T {4, 5, 6} → False := by
  intro a131 a85 a101
  have hc := h.complementary {0, 1, 3, 7} {2, 8, 9} a131 (by decide) (by decide)
  have he : ( {0, 1, 3, 7} : Finset Labels)ᶜ \ {2, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a85 a101

theorem c3231 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a131 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {2, 5} {4, 6, 8} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c3295 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 6} → T {4, 5, 6} → T {5, 6, 8} → False := by
  intro a131 a76 a101 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 6} {2, 4, 8} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)

theorem c3297 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 6} → T {4, 5, 6} → T {5, 6, 9} → False := by
  intro a131 a76 a101 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 6} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c3304 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a131 n78 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 3, 7} {5, 8} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c3305 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a131 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 8} {2, 4, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c3307 (h : TenSystem T Q) :
    Q {0, 1, 3, 7} → T {2, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a131 a78 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 7} {5, 8} {2, 6, 9} a131 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c3343 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {6, 7, 9} → False := by
  intro a132 a71 a118
  have hc := h.complementary {0, 1, 3, 8} {2, 4, 5} a132 (by decide) (by decide)
  have he : ( {0, 1, 3, 8} : Finset Labels)ᶜ \ {2, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a118

theorem c3351 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 5, 6} → T {4, 7, 9} → False := by
  intro a132 a76 a109
  have hc := h.complementary {0, 1, 3, 8} {2, 5, 6} a132 (by decide) (by decide)
  have he : ( {0, 1, 3, 8} : Finset Labels)ᶜ \ {2, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a76 a109

theorem c3363 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {2, 4, 6} → T {2, 4, 7} → False := by
  intro a132 a71 a72 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 8} {2, 4} {5, 6, 7} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c3371 (h : TenSystem T Q) :
    Q {0, 1, 3, 8} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 7} → False := by
  intro a132 a71 a76 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 3, 8} {2, 5} {4, 6, 7} a132 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

end BorsukNine.FiniteObstruction

end OAI
