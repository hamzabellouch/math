import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c15261 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 8, 9} → T {3, 4, 6} → False := by
  intro a217 a36 a87
  have hc := h.complementary {1, 2, 5, 7} {0, 8, 9} a217 (by decide) (by decide)
  have he : ( {1, 2, 5, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a36 a87

theorem c15273 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 3, 4} → T {0, 4, 6} → T {0, 4, 9} → False := by
  intro a217 a16 a23 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 7} {0, 4} {3, 6, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 4} = {0, 4, 9} by decide)) a26)

theorem c15336 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a217 n23 n87 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 7} {4, 6} {0, 3, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c15337 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 9} → False := by
  intro a217 a23 a87 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 7} {4, 6} {0, 3, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c15360 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a217 n32 n96 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 7} {6, 8} {0, 3, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c15364 (h : TenSystem T Q) :
    Q {1, 2, 5, 7} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a217 n96 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 7} {6, 8} {3, 4, 9} a217 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c15391 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 4, 6} → T {3, 7, 9} → False := by
  intro a218 a23 a99
  have hc := h.complementary {1, 2, 5, 8} {0, 4, 6} a218 (by decide) (by decide)
  have he : ( {1, 2, 5, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a99

theorem c15397 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 6, 7} → T {3, 4, 9} → False := by
  intro a218 a31 a90
  have hc := h.complementary {1, 2, 5, 8} {0, 6, 7} a218 (by decide) (by decide)
  have he : ( {1, 2, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a31 a90

theorem c15437 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a218 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {0, 9} {3, 4, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c15483 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a218 a24 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {4, 7} {0, 3, 6} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c15489 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a218 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {4, 7} {3, 6, 9} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c15497 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a218 a90 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {4, 9} {3, 6, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c15505 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a218 a95 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {6, 7} {3, 4, 9} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c15510 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → ¬ T {0, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a218 n33 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 8} {6, 9} {0, 4, 7} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c15519 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {0, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a218 a35 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {7, 9} {0, 4, 6} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c15521 (h : TenSystem T Q) :
    Q {1, 2, 5, 8} → T {3, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a218 a99 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 8} {7, 9} {3, 4, 6} a218 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c15528 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 3, 8} → ¬ T {4, 6, 7} → False := by
  intro a219 n20 n105
  have hc := h.complementary {1, 2, 5, 9} {0, 3, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n105)

theorem c15529 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 3, 8} → T {4, 6, 7} → False := by
  intro a219 a20 a105
  have hc := h.complementary {1, 2, 5, 9} {0, 3, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a20 a105

theorem c15532 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → ¬ T {3, 6, 8} → False := by
  intro a219 n24 n96
  have hc := h.complementary {1, 2, 5, 9} {0, 4, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n96)

theorem c15533 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 4, 7} → T {3, 6, 8} → False := by
  intro a219 a24 a96
  have hc := h.complementary {1, 2, 5, 9} {0, 4, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a96

theorem c15537 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 6, 7} → T {3, 4, 8} → False := by
  intro a219 a31 a89
  have hc := h.complementary {1, 2, 5, 9} {0, 6, 7} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a89

theorem c15538 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 6, 8} → ¬ T {3, 4, 7} → False := by
  intro a219 n32 n88
  have hc := h.complementary {1, 2, 5, 9} {0, 6, 8} a219 (by decide) (by decide)
  have he : ( {1, 2, 5, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n88)

theorem c15567 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 3, 7} → T {0, 4, 7} → T {0, 6, 7} → False := by
  intro a219 a19 a24 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 9} {0, 7} {3, 4, 6} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c15614 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a219 n23 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 9} {4, 6} {0, 3, 7} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c15622 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a219 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 9} {4, 7} {0, 3, 6} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c15623 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a219 a24 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 9} {4, 7} {0, 3, 6} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c15638 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a219 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 5, 9} {6, 7} {0, 3, 4} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c15651 (h : TenSystem T Q) :
    Q {1, 2, 5, 9} → T {0, 6, 8} → T {4, 6, 8} → T {6, 7, 8} → False := by
  intro a219 a32 a106 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 5, 9} {6, 8} {0, 4, 7} a219 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c15662 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 3, 4} → ¬ T {5, 8, 9} → False := by
  intro a220 n16 n116
  have hc := h.complementary {1, 2, 6, 7} {0, 3, 4} a220 (by decide) (by decide)
  have he : ( {1, 2, 6, 7} : Finset Labels)ᶜ \ {0, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n116)

theorem c15669 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 3, 9} → T {4, 5, 8} → False := by
  intro a220 a21 a103
  have hc := h.complementary {1, 2, 6, 7} {0, 3, 9} a220 (by decide) (by decide)
  have he : ( {1, 2, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a103

theorem c15719 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 3, 9} → T {0, 5, 9} → T {0, 8, 9} → False := by
  intro a220 a21 a30 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 7} {0, 9} {3, 5, 8} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c15738 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 3, 8} → ¬ T {3, 4, 8} → ¬ T {3, 5, 8} → False := by
  intro a220 n20 n89 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {3, 8} {0, 4, 5} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n20 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 8} = {0, 3, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 8} = {3, 5, 8} by decide)) ht)

theorem c15758 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a220 n22 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {4, 5} {0, 8, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c15766 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → ¬ T {0, 4, 8} → ¬ T {4, 5, 8} → ¬ T {4, 8, 9} → False := by
  intro a220 n25 n103 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 7} {4, 8} {0, 5, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c15781 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 5, 8} → T {3, 5, 8} → T {5, 8, 9} → False := by
  intro a220 a29 a93 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 7} {5, 8} {0, 3, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c15783 (h : TenSystem T Q) :
    Q {1, 2, 6, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a220 a29 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 7} {5, 8} {0, 4, 9} a220 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c15811 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 4, 5} → T {3, 7, 9} → False := by
  intro a221 a22 a99
  have hc := h.complementary {1, 2, 6, 8} {0, 4, 5} a221 (by decide) (by decide)
  have he : ( {1, 2, 6, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a99

theorem c15857 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 3, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a221 a21 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {0, 9} {3, 4, 7} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c15869 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a221 a86 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {3, 4} {5, 7, 9} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c15888 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → ¬ T {0, 3, 9} → ¬ T {3, 4, 9} → ¬ T {3, 7, 9} → False := by
  intro a221 n21 n90 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 8} {3, 9} {0, 4, 7} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c15915 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 4, 9} → T {4, 5, 9} → T {4, 7, 9} → False := by
  intro a221 a26 a104 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {4, 9} {0, 5, 7} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c15939 (h : TenSystem T Q) :
    Q {1, 2, 6, 8} → T {0, 7, 9} → T {4, 7, 9} → T {5, 7, 9} → False := by
  intro a221 a35 a109 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 8} {7, 9} {0, 4, 5} a221 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)

theorem c15945 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 3, 5} → T {4, 7, 8} → False := by
  intro a222 a17 a108
  have hc := h.complementary {1, 2, 6, 9} {0, 3, 5} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a17 a108

theorem c15946 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {0, 3, 7} → ¬ T {4, 5, 8} → False := by
  intro a222 n19 n103
  have hc := h.complementary {1, 2, 6, 9} {0, 3, 7} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n103)

theorem c15947 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 3, 7} → T {4, 5, 8} → False := by
  intro a222 a19 a103
  have hc := h.complementary {1, 2, 6, 9} {0, 3, 7} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a19 a103

end BorsukNine.FiniteObstruction

end OAI
