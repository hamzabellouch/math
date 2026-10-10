import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c21327 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 6} → False := by
  intro a260 a9 a66 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 7, 8, 9} {2, 3} {0, 5, 6} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c21332 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 6} → False := by
  intro a260 n10 n65 n72
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 7, 8, 9} {2, 4} {0, 3, 6} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) ht)

theorem c21337 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a260 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 7, 8, 9} {2, 4} {3, 5, 6} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c21387 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {0, 4, 6} → T {2, 4, 6} → T {3, 4, 6} → False := by
  intro a260 a23 a72 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 7, 8, 9} {4, 6} {0, 2, 3} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c21404 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ T {0, 1, 7} → ¬ T {6, 8, 9} → False := by
  intro a261 n6 n119
  have hc := h.complementary {2, 3, 4, 5} {0, 1, 7} a261 (by decide) (by decide)
  have he : ( {2, 3, 4, 5} : Finset Labels)ᶜ \ {0, 1, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n119)

theorem c21405 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → T {0, 1, 7} → T {6, 8, 9} → False := by
  intro a261 a6 a119
  have hc := h.complementary {2, 3, 4, 5} {0, 1, 7} a261 (by decide) (by decide)
  have he : ( {2, 3, 4, 5} : Finset Labels)ᶜ \ {0, 1, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a119

theorem c21408 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → ¬ T {0, 1, 9} → ¬ T {6, 7, 8} → False := by
  intro a261 n8 n117
  have hc := h.complementary {2, 3, 4, 5} {0, 1, 9} a261 (by decide) (by decide)
  have he : ( {2, 3, 4, 5} : Finset Labels)ᶜ \ {0, 1, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n117)

theorem c21523 (h : TenSystem T Q) :
    Q {2, 3, 4, 5} → T {0, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a261 a34 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 5} {7, 8} {0, 6, 9} a261 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 8} = {0, 7, 8} by decide)) a34)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c21543 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 1, 5} → T {7, 8, 9} → False := by
  intro a262 a4 a120
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 5} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a4 a120

theorem c21544 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {0, 1, 7} → ¬ T {5, 8, 9} → False := by
  intro a262 n6 n116
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n116)

theorem c21545 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 1, 7} → T {5, 8, 9} → False := by
  intro a262 a6 a116
  have hc := h.complementary {2, 3, 4, 6} {0, 1, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a116

theorem c21551 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 5, 7} → T {1, 8, 9} → False := by
  intro a262 a28 a64
  have hc := h.complementary {2, 3, 4, 6} {0, 5, 7} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a64

theorem c21553 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 5, 8} → T {1, 7, 9} → False := by
  intro a262 a29 a63
  have hc := h.complementary {2, 3, 4, 6} {0, 5, 8} a262 (by decide) (by decide)
  have he : ( {2, 3, 4, 6} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a63

theorem c21644 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a262 n29 n57 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 6} {5, 8} {0, 1, 9} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c21645 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a262 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {5, 8} {0, 1, 9} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c21646 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → ¬ T {0, 5, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a262 n29 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 6} {5, 8} {0, 7, 9} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c21657 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {1, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a262 a58 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {5, 9} {1, 7, 8} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c21681 (h : TenSystem T Q) :
    Q {2, 3, 4, 6} → T {1, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a262 a64 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 6} {8, 9} {1, 5, 7} a262 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c21682 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 1, 5} → ¬ T {6, 8, 9} → False := by
  intro a263 n4 n119
  have hc := h.complementary {2, 3, 4, 7} {0, 1, 5} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n119)

theorem c21684 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 1, 6} → ¬ T {5, 8, 9} → False := by
  intro a263 n5 n116
  have hc := h.complementary {2, 3, 4, 7} {0, 1, 6} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n116)

theorem c21699 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 6, 9} → T {1, 5, 8} → False := by
  intro a263 a33 a57
  have hc := h.complementary {2, 3, 4, 7} {0, 6, 9} a263 (by decide) (by decide)
  have he : ( {2, 3, 4, 7} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a33 a57

theorem c21737 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 1, 9} → T {0, 5, 9} → T {0, 8, 9} → False := by
  intro a263 a8 a30 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {0, 9} {1, 5, 8} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c21785 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a263 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {5, 8} {0, 1, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c21786 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a263 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c21787 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a263 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {5, 8} {0, 6, 9} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c21821 (h : TenSystem T Q) :
    Q {2, 3, 4, 7} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a263 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 7} {8, 9} {1, 5, 6} a263 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c21822 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 5} → ¬ T {6, 7, 9} → False := by
  intro a264 n4 n118
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 5} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n118)

theorem c21824 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 6} → ¬ T {5, 7, 9} → False := by
  intro a264 n5 n115
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 6} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n115)

theorem c21827 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {0, 1, 7} → T {5, 6, 9} → False := by
  intro a264 a6 a113
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 7} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a113

theorem c21828 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 9} → ¬ T {5, 6, 7} → False := by
  intro a264 n8 n111
  have hc := h.complementary {2, 3, 4, 8} {0, 1, 9} a264 (by decide) (by decide)
  have he : ( {2, 3, 4, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n111)

theorem c21842 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a264 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 8} {0, 1} {5, 6, 7} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c21937 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {1, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a264 a58 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 8} {5, 9} {1, 6, 7} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c21945 (h : TenSystem T Q) :
    Q {2, 3, 4, 8} → T {1, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a264 a59 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 8} {6, 7} {1, 5, 9} a264 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c21962 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 5} → ¬ T {6, 7, 8} → False := by
  intro a265 n4 n117
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 5} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n117)

theorem c21964 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 6} → ¬ T {5, 7, 8} → False := by
  intro a265 n5 n114
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 6} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n114)

theorem c21965 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 1, 6} → T {5, 7, 8} → False := by
  intro a265 a5 a114
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 6} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a5 a114

theorem c21967 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 1, 7} → T {5, 6, 8} → False := by
  intro a265 a6 a112
  have hc := h.complementary {2, 3, 4, 9} {0, 1, 7} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a6 a112

theorem c21975 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 5, 8} → T {1, 6, 7} → False := by
  intro a265 a29 a59
  have hc := h.complementary {2, 3, 4, 9} {0, 5, 8} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a59

theorem c21981 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 7, 8} → T {1, 5, 6} → False := by
  intro a265 a34 a55
  have hc := h.complementary {2, 3, 4, 9} {0, 7, 8} a265 (by decide) (by decide)
  have he : ( {2, 3, 4, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a34 a55

theorem c21982 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a265 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {0, 1} {5, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c22005 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 5, 6} → T {0, 6, 7} → T {0, 6, 8} → False := by
  intro a265 a27 a31 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {0, 6} {5, 7, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) a32)

theorem c22034 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 1, 6} → ¬ T {1, 6, 7} → ¬ T {1, 6, 8} → False := by
  intro a265 n5 n59 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {1, 6} {0, 7, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

theorem c22045 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a265 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {1, 7} {5, 6, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

theorem c22074 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a265 n29 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {5, 8} {0, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c22075 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a265 a29 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {5, 8} {0, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c22076 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a265 n57 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {5, 8} {1, 6, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c22083 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → T {0, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a265 a31 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 4, 9} {6, 7} {0, 5, 8} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

end BorsukNine.FiniteObstruction

end OAI
