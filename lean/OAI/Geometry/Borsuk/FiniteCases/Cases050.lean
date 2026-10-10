import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c17174 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a230 n29 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {5, 8} {0, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c17176 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a230 n78 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {5, 8} {2, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c17203 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 4} → T {7, 8, 9} → False := by
  intro a231 a10 a120
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 4} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a120

theorem c17205 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 7} → T {4, 8, 9} → False := by
  intro a231 a13 a110
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 7} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a110

theorem c17207 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 8} → T {4, 7, 9} → False := by
  intro a231 a14 a109
  have hc := h.complementary {1, 3, 5, 6} {0, 2, 8} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a14 a109

theorem c17211 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 7} → T {2, 8, 9} → False := by
  intro a231 a24 a85
  have hc := h.complementary {1, 3, 5, 6} {0, 4, 7} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a85

theorem c17219 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 7, 9} → T {2, 4, 8} → False := by
  intro a231 a35 a74
  have hc := h.complementary {1, 3, 5, 6} {0, 7, 9} a231 (by decide) (by decide)
  have he : ( {1, 3, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a35 a74

theorem c17240 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 2, 7} → ¬ T {0, 4, 7} → ¬ T {0, 7, 9} → False := by
  intro a231 n13 n24 n35
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {0, 7} {2, 4, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) ht)
  · exact n35 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 7} = {0, 7, 9} by decide)) ht)

theorem c17255 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a231 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {0, 9} {2, 4, 7} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c17257 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 2, 9} → T {0, 4, 9} → T {0, 8, 9} → False := by
  intro a231 a15 a26 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {0, 9} {2, 4, 8} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c17297 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a231 a24 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {4, 7} {0, 2, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c17298 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a231 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c17299 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a231 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {4, 7} {0, 8, 9} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c17315 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a231 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {4, 9} {0, 7, 8} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c17331 (h : TenSystem T Q) :
    Q {1, 3, 5, 6} → T {0, 7, 9} → T {4, 7, 9} → T {7, 8, 9} → False := by
  intro a231 a35 a109 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 6} {7, 9} {0, 4, 8} a231 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c17342 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 4} → ¬ T {6, 8, 9} → False := by
  intro a232 n10 n119
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 4} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n119)

theorem c17343 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {6, 8, 9} → False := by
  intro a232 a10 a119
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 4} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a119

theorem c17344 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 6} → ¬ T {4, 8, 9} → False := by
  intro a232 n12 n110
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 6} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n110)

theorem c17346 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 8} → ¬ T {4, 6, 9} → False := by
  intro a232 n14 n107
  have hc := h.complementary {1, 3, 5, 7} {0, 2, 8} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n107)

theorem c17351 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 4, 6} → T {2, 8, 9} → False := by
  intro a232 a23 a85
  have hc := h.complementary {1, 3, 5, 7} {0, 4, 6} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a85

theorem c17357 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 6, 8} → T {2, 4, 9} → False := by
  intro a232 a32 a75
  have hc := h.complementary {1, 3, 5, 7} {0, 6, 8} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a75

theorem c17361 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 8, 9} → T {2, 4, 6} → False := by
  intro a232 a36 a72
  have hc := h.complementary {1, 3, 5, 7} {0, 8, 9} a232 (by decide) (by decide)
  have he : ( {1, 3, 5, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a36 a72

theorem c17365 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a232 a10 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 2} {4, 6, 9} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c17373 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 9} → False := by
  intro a232 a10 a23 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 4} {2, 6, 9} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 4} = {0, 4, 9} by decide)) a26)

theorem c17378 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 6} → ¬ T {0, 4, 6} → ¬ T {0, 6, 8} → False := by
  intro a232 n12 n23 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 7} {0, 6} {2, 4, 8} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

theorem c17387 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 2, 8} → T {0, 4, 8} → T {0, 6, 8} → False := by
  intro a232 a14 a25 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {0, 8} {2, 4, 6} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c17426 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a232 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 7} {2, 9} {0, 4, 6} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c17437 (h : TenSystem T Q) :
    Q {1, 3, 5, 7} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 9} → False := by
  intro a232 a23 a72 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 7} {4, 6} {0, 2, 9} a232 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17483 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 4} → T {6, 7, 9} → False := by
  intro a233 a10 a118
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 4} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a118

theorem c17484 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 2, 6} → ¬ T {4, 7, 9} → False := by
  intro a233 n12 n109
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 6} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n109)

theorem c17485 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 6} → T {4, 7, 9} → False := by
  intro a233 a12 a109
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 6} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a12 a109

theorem c17487 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 7} → T {4, 6, 9} → False := by
  intro a233 a13 a107
  have hc := h.complementary {1, 3, 5, 8} {0, 2, 7} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a107

theorem c17493 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {2, 6, 9} → False := by
  intro a233 a24 a82
  have hc := h.complementary {1, 3, 5, 8} {0, 4, 7} a233 (by decide) (by decide)
  have he : ( {1, 3, 5, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a82

theorem c17511 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a233 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 4} {2, 6, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c17535 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a233 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 9} {2, 4, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c17537 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a233 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {0, 9} {2, 4, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c17552 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 9} → False := by
  intro a233 n12 n72 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {2, 6} {0, 4, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) ht)

theorem c17575 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a233 a23 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 2, 7} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c17576 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 4, 6} → ¬ T {2, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a233 n23 n72 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 6} {0, 2, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c17577 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 9} → False := by
  intro a233 a23 a72 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 2, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17578 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a233 n23 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 6} {0, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c17579 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a233 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {0, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17581 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {2, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a233 a72 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 6} {2, 7, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c17583 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {2, 4, 7} → T {4, 6, 7} → False := by
  intro a233 a24 a73 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 7} {0, 2, 6} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c17585 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → T {0, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a233 a24 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 5, 8} {4, 7} {0, 2, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c17586 (h : TenSystem T Q) :
    Q {1, 3, 5, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a233 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 5, 8} {4, 7} {0, 6, 9} a233 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
