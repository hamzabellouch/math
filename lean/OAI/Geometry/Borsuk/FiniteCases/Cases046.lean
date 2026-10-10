import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c14299 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 7} → False := by
  intro a210 a23 a27 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 6} {4, 5, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)

theorem c14315 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a210 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 8} {4, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c14330 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a210 n23 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 6} {0, 5, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c14331 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a210 a23 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 6} {0, 5, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c14332 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 8} → False := by
  intro a210 n23 n101 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 6} {0, 5, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)

theorem c14338 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → False := by
  intro a210 n24 n102 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 7} {0, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c14339 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 6, 7} → False := by
  intro a210 a24 a102 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 7} {0, 5, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c14342 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → False := by
  intro a210 n24 n105 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {4, 7} {0, 6, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)

theorem c14343 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 8} → False := by
  intro a210 a24 a105 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {4, 7} {0, 6, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c14370 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a210 n29 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {5, 8} {0, 4, 6} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c14373 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a210 a29 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {5, 8} {0, 4, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c14374 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a210 n29 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 9} {5, 8} {0, 6, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c14404 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → ¬ T {0, 3, 7} → ¬ T {6, 8, 9} → False := by
  intro a211 n19 n119
  have hc := h.complementary {1, 2, 4, 5} {0, 3, 7} a211 (by decide) (by decide)
  have he : ( {1, 2, 4, 5} : Finset Labels)ᶜ \ {0, 3, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n119)

theorem c14497 (h : TenSystem T Q) :
    Q {1, 2, 4, 5} → T {0, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a211 a31 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 5} {6, 7} {0, 3, 9} a211 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c14544 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → ¬ T {0, 3, 7} → ¬ T {5, 8, 9} → False := by
  intro a212 n19 n116
  have hc := h.complementary {1, 2, 4, 6} {0, 3, 7} a212 (by decide) (by decide)
  have he : ( {1, 2, 4, 6} : Finset Labels)ᶜ \ {0, 3, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n116)

theorem c14549 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {0, 3, 9} → T {5, 7, 8} → False := by
  intro a212 a21 a114
  have hc := h.complementary {1, 2, 4, 6} {0, 3, 9} a212 (by decide) (by decide)
  have he : ( {1, 2, 4, 6} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a114

theorem c14597 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {0, 3, 9} → T {0, 5, 9} → T {0, 8, 9} → False := by
  intro a212 a21 a30 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 6} {0, 9} {3, 5, 8} a212 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c14645 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a212 a29 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 6} {5, 8} {0, 3, 9} a212 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c14681 (h : TenSystem T Q) :
    Q {1, 2, 4, 6} → T {3, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a212 a100 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 6} {8, 9} {3, 5, 7} a212 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c14685 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → T {0, 3, 6} → T {5, 8, 9} → False := by
  intro a213 a18 a116
  have hc := h.complementary {1, 2, 4, 7} {0, 3, 6} a213 (by decide) (by decide)
  have he : ( {1, 2, 4, 7} : Finset Labels)ᶜ \ {0, 3, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a18 a116

theorem c14689 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → T {0, 3, 9} → T {5, 6, 8} → False := by
  intro a213 a21 a112
  have hc := h.complementary {1, 2, 4, 7} {0, 3, 9} a213 (by decide) (by decide)
  have he : ( {1, 2, 4, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a112

theorem c14786 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a213 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 4, 7} {5, 8} {0, 6, 9} a213 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c14804 (h : TenSystem T Q) :
    Q {1, 2, 4, 7} → ¬ T {3, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a213 n96 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 4, 7} {6, 8} {3, 5, 9} a213 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c14826 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → ¬ T {0, 3, 7} → ¬ T {5, 6, 9} → False := by
  intro a214 n19 n113
  have hc := h.complementary {1, 2, 4, 8} {0, 3, 7} a214 (by decide) (by decide)
  have he : ( {1, 2, 4, 8} : Finset Labels)ᶜ \ {0, 3, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n113)

theorem c14828 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → ¬ T {0, 3, 9} → ¬ T {5, 6, 7} → False := by
  intro a214 n21 n111
  have hc := h.complementary {1, 2, 4, 8} {0, 3, 9} a214 (by decide) (by decide)
  have he : ( {1, 2, 4, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n111)

theorem c14937 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → T {3, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a214 a94 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 8} {5, 9} {3, 6, 7} a214 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c14941 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → T {0, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a214 a31 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 8} {6, 7} {0, 3, 9} a214 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c14945 (h : TenSystem T Q) :
    Q {1, 2, 4, 8} → T {3, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a214 a95 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 8} {6, 7} {3, 5, 9} a214 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c14966 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {0, 3, 7} → ¬ T {5, 6, 8} → False := by
  intro a215 n19 n112
  have hc := h.complementary {1, 2, 4, 9} {0, 3, 7} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n112)

theorem c14967 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 3, 7} → T {5, 6, 8} → False := by
  intro a215 a19 a112
  have hc := h.complementary {1, 2, 4, 9} {0, 3, 7} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a19 a112

theorem c14975 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 5, 8} → T {3, 6, 7} → False := by
  intro a215 a29 a95
  have hc := h.complementary {1, 2, 4, 9} {0, 5, 8} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a95

theorem c14977 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 6, 7} → T {3, 5, 8} → False := by
  intro a215 a31 a93
  have hc := h.complementary {1, 2, 4, 9} {0, 6, 7} a215 (by decide) (by decide)
  have he : ( {1, 2, 4, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a93

theorem c15071 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {0, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a215 a29 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {0, 3, 6} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c15072 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a215 n29 n93 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 4, 9} {5, 8} {0, 3, 7} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c15077 (h : TenSystem T Q) :
    Q {1, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a215 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 4, 9} {5, 8} {3, 6, 7} a215 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c15104 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → ¬ T {0, 3, 7} → ¬ T {4, 8, 9} → False := by
  intro a216 n19 n110
  have hc := h.complementary {1, 2, 5, 6} {0, 3, 7} a216 (by decide) (by decide)
  have he : ( {1, 2, 5, 6} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n110)

theorem c15119 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 7, 9} → T {3, 4, 8} → False := by
  intro a216 a35 a89
  have hc := h.complementary {1, 2, 5, 6} {0, 7, 9} a216 (by decide) (by decide)
  have he : ( {1, 2, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a89

theorem c15155 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a216 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {0, 9} {3, 4, 7} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c15169 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {3, 4, 7} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a216 a88 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {3, 4} {7, 8, 9} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c15187 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a216 a21 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {3, 9} {0, 4, 7} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c15215 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a216 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {4, 9} {0, 7, 8} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c15231 (h : TenSystem T Q) :
    Q {1, 2, 5, 6} → T {0, 7, 9} → T {4, 7, 9} → T {7, 8, 9} → False := by
  intro a216 a35 a109 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 6} {7, 9} {0, 4, 8} a216 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c15242 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 3, 4} → ¬ T {6, 8, 9} → False := by
  intro a217 n16 n119
  have hc := h.complementary {1, 2, 5, 7} {0, 3, 4} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 3, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n119)

theorem c15246 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 3, 8} → ¬ T {4, 6, 9} → False := by
  intro a217 n20 n107
  have hc := h.complementary {1, 2, 5, 7} {0, 3, 8} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n107)

theorem c15250 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 4, 6} → ¬ T {3, 8, 9} → False := by
  intro a217 n23 n100
  have hc := h.complementary {1, 2, 5, 7} {0, 4, 6} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n100)

theorem c15257 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 6, 8} → T {3, 4, 9} → False := by
  intro a217 a32 a90
  have hc := h.complementary {1, 2, 5, 7} {0, 6, 8} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a90

end BorsukNine.FiniteObstruction

end OAI
