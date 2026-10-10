import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c13399 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {3, 4, 5} → False := by
  intro a203 a50 a71 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {4, 5} {1, 2, 3} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

theorem c13407 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a203 a52 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {4, 7} {1, 2, 3} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c13423 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 3} → T {4, 5, 6} → False := by
  intro a204 a37 a101
  have hc := h.complementary {0, 7, 8, 9} {1, 2, 3} a204 (by decide) (by decide)
  have he : ( {0, 7, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a37 a101

theorem c13425 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 4} → T {3, 5, 6} → False := by
  intro a204 a38 a91
  have hc := h.complementary {0, 7, 8, 9} {1, 2, 4} a204 (by decide) (by decide)
  have he : ( {0, 7, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a38 a91

theorem c13439 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 4, 6} → T {2, 3, 5} → False := by
  intro a204 a51 a66
  have hc := h.complementary {0, 7, 8, 9} {1, 4, 6} a204 (by decide) (by decide)
  have he : ( {0, 7, 8, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 3, 5} := by decide
  rw [he] at hc
  exact hc.mp a51 a66

theorem c13455 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a204 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 7, 8, 9} {1, 3} {2, 5, 6} a204 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c13497 (h : TenSystem T Q) :
    Q {0, 7, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a204 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 7, 8, 9} {2, 4} {3, 5, 6} a204 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c13562 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 6} → ¬ T {7, 8, 9} → False := by
  intro a205 n27 n120
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 6} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n120)

theorem c13563 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 6} → T {7, 8, 9} → False := by
  intro a205 a27 a120
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 6} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a120

theorem c13566 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a205 n29 n118
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n118)

theorem c13567 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 8} → T {6, 7, 9} → False := by
  intro a205 a29 a118
  have hc := h.complementary {1, 2, 3, 4} {0, 5, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a118

theorem c13571 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 6, 7} → T {5, 8, 9} → False := by
  intro a205 a31 a116
  have hc := h.complementary {1, 2, 3, 4} {0, 6, 7} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a31 a116

theorem c13572 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 6, 8} → ¬ T {5, 7, 9} → False := by
  intro a205 n32 n115
  have hc := h.complementary {1, 2, 3, 4} {0, 6, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n115)

theorem c13574 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 6, 9} → ¬ T {5, 7, 8} → False := by
  intro a205 n33 n114
  have hc := h.complementary {1, 2, 3, 4} {0, 6, 9} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n114)

theorem c13575 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 6, 9} → T {5, 7, 8} → False := by
  intro a205 a33 a114
  have hc := h.complementary {1, 2, 3, 4} {0, 6, 9} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a33 a114

theorem c13577 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 7, 8} → T {5, 6, 9} → False := by
  intro a205 a34 a113
  have hc := h.complementary {1, 2, 3, 4} {0, 7, 8} a205 (by decide) (by decide)
  have he : ( {1, 2, 3, 4} : Finset Labels)ᶜ \ {0, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a34 a113

theorem c13592 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 6} → ¬ T {0, 6, 7} → ¬ T {0, 6, 9} → False := by
  intro a205 n27 n31 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 4} {0, 6} {5, 7, 9} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) ht)
  · exact n31 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c13631 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 7} → T {5, 6, 7} → T {5, 7, 8} → False := by
  intro a205 a28 a111 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 4} {5, 7} {0, 6, 8} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) a114)

theorem c13640 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a205 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 4} {5, 8} {0, 6, 9} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c13641 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a205 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 4} {5, 8} {0, 6, 9} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c13649 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → T {0, 5, 9} → T {5, 6, 9} → T {5, 8, 9} → False := by
  intro a205 a30 a113 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 4} {5, 9} {0, 6, 8} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c13698 (h : TenSystem T Q) :
    Q {1, 2, 3, 4} → ¬ T {0, 8, 9} → ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a205 n36 n119 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 4} {8, 9} {0, 6, 7} a205 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n36 (Eq.mp (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c13702 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {0, 4, 6} → ¬ T {7, 8, 9} → False := by
  intro a206 n23 n120
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 6} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n120)

theorem c13703 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 6} → T {7, 8, 9} → False := by
  intro a206 a23 a120
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 6} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a120

theorem c13709 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {6, 7, 8} → False := by
  intro a206 a26 a117
  have hc := h.complementary {1, 2, 3, 5} {0, 4, 9} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 4, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a26 a117

theorem c13719 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 7, 9} → T {4, 6, 8} → False := by
  intro a206 a35 a106
  have hc := h.complementary {1, 2, 3, 5} {0, 7, 9} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 7, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a106

theorem c13720 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {0, 8, 9} → ¬ T {4, 6, 7} → False := by
  intro a206 n36 n105
  have hc := h.complementary {1, 2, 3, 5} {0, 8, 9} a206 (by decide) (by decide)
  have he : ( {1, 2, 3, 5} : Finset Labels)ᶜ \ {0, 8, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n36 (hc.mpr n105)

theorem c13757 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {0, 6, 9} → T {0, 8, 9} → False := by
  intro a206 a26 a33 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {0, 9} {4, 6, 8} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c13772 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a206 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 5} {4, 7} {0, 6, 9} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c13773 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a206 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 7} {0, 6, 9} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c13775 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a206 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 7} {0, 8, 9} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c13787 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a206 a26 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 9} {0, 6, 7} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c13791 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a206 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {4, 9} {0, 7, 8} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c13827 (h : TenSystem T Q) :
    Q {1, 2, 3, 5} → T {0, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a206 a35 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 5} {7, 9} {0, 4, 6} a206 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c13842 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a207 n22 n120
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 5} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n120)

theorem c13843 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 4, 5} → T {7, 8, 9} → False := by
  intro a207 a22 a120
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 5} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a120

theorem c13844 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a207 n24 n116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n116)

theorem c13845 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 4, 7} → T {5, 8, 9} → False := by
  intro a207 a24 a116
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a116

theorem c13849 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 4, 9} → T {5, 7, 8} → False := by
  intro a207 a26 a114
  have hc := h.complementary {1, 2, 3, 6} {0, 4, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 4, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a26 a114

theorem c13850 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 5, 7} → ¬ T {4, 8, 9} → False := by
  intro a207 n28 n110
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 7} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n110)

theorem c13852 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → ¬ T {0, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a207 n29 n109
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 8} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n109)

theorem c13853 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 5, 8} → T {4, 7, 9} → False := by
  intro a207 a29 a109
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 8} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a109

theorem c13855 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 5, 9} → T {4, 7, 8} → False := by
  intro a207 a30 a108
  have hc := h.complementary {1, 2, 3, 6} {0, 5, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 5, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a30 a108

theorem c13859 (h : TenSystem T Q) :
    Q {1, 2, 3, 6} → T {0, 7, 9} → T {4, 5, 8} → False := by
  intro a207 a35 a103
  have hc := h.complementary {1, 2, 3, 6} {0, 7, 9} a207 (by decide) (by decide)
  have he : ( {1, 2, 3, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a103

theorem c13982 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 4, 5} → ¬ T {6, 8, 9} → False := by
  intro a208 n22 n119
  have hc := h.complementary {1, 2, 3, 7} {0, 4, 5} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n119)

theorem c13983 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 5} → T {6, 8, 9} → False := by
  intro a208 a22 a119
  have hc := h.complementary {1, 2, 3, 7} {0, 4, 5} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a119

theorem c13985 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 6} → T {5, 8, 9} → False := by
  intro a208 a23 a116
  have hc := h.complementary {1, 2, 3, 7} {0, 4, 6} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a116

theorem c13987 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 8} → T {5, 6, 9} → False := by
  intro a208 a25 a113
  have hc := h.complementary {1, 2, 3, 7} {0, 4, 8} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 4, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a25 a113

theorem c13993 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {4, 6, 9} → False := by
  intro a208 a29 a107
  have hc := h.complementary {1, 2, 3, 7} {0, 5, 8} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a107

end BorsukNine.FiniteObstruction

end OAI
