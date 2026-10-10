import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c27508 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 6, 8} → False := by
  intro a304 n7 n42 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {1, 8} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) ht)

theorem c27540 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 6} → ¬ T {1, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a304 n27 n55 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {5, 6} {0, 1, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c27548 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a304 n29 n57 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {5, 8} {0, 1, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c27550 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a304 n29 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {5, 8} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c27563 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {5, 6, 7} → False := by
  intro a305 a1 a111
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 2} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a111

theorem c27566 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 6} → ¬ T {2, 5, 7} → False := by
  intro a305 n5 n77
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n77)

theorem c27569 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 7} → T {2, 5, 6} → False := by
  intro a305 a6 a76
  have hc := h.complementary {3, 4, 8, 9} {0, 1, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a6 a76

theorem c27571 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 5} → T {1, 6, 7} → False := by
  intro a305 a11 a59
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 5} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a11 a59

theorem c27572 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 5, 7} → False := by
  intro a305 n12 n56
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n56)

theorem c27573 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 6} → T {1, 5, 7} → False := by
  intro a305 a12 a56
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 6} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a56

theorem c27575 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {1, 5, 6} → False := by
  intro a305 a13 a55
  have hc := h.complementary {3, 4, 8, 9} {0, 2, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a55

theorem c27578 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 7} → ¬ T {1, 2, 6} → False := by
  intro a305 n28 n40
  have hc := h.complementary {3, 4, 8, 9} {0, 5, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n40)

theorem c27580 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 5} → False := by
  intro a305 n31 n39
  have hc := h.complementary {3, 4, 8, 9} {0, 6, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n39)

theorem c27581 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 6, 7} → T {1, 2, 5} → False := by
  intro a305 a31 a39
  have hc := h.complementary {3, 4, 8, 9} {0, 6, 7} a305 (by decide) (by decide)
  have he : ( {3, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact hc.mp a31 a39

theorem c27587 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 7} → False := by
  intro a305 a1 a5 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {0, 1} {2, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c27588 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a305 n4 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {0, 1} {5, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c27595 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a305 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {0, 2} {1, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27621 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {0, 5, 7} → T {0, 6, 7} → False := by
  intro a305 a13 a28 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {0, 7} {2, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c27623 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a305 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {1, 2} {0, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c27628 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {1, 2, 5} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → False := by
  intro a305 n39 n40 n41
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {1, 2} {5, 6, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n39 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)

theorem c27640 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 1, 6} → ¬ T {1, 2, 6} → ¬ T {1, 6, 7} → False := by
  intro a305 n5 n40 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {1, 6} {0, 2, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c27667 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a305 a12 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {2, 6} {0, 5, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c27675 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a305 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {2, 7} {0, 5, 6} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c27680 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {1, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a305 n27 n55 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {5, 6} {0, 1, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c27682 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a305 n27 n76 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 8, 9} {5, 6} {0, 2, 7} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c27695 (h : TenSystem T Q) :
    Q {3, 4, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {2, 6, 7} → False := by
  intro a305 a31 a59 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 8, 9} {6, 7} {0, 1, 2} a305 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)

theorem c27703 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 1, 2} → T {4, 8, 9} → False := by
  intro a306 a1 a110
  have hc := h.complementary {3, 5, 6, 7} {0, 1, 2} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a110

theorem c27704 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 1, 4} → ¬ T {2, 8, 9} → False := by
  intro a306 n3 n85
  have hc := h.complementary {3, 5, 6, 7} {0, 1, 4} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 8, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n85)

theorem c27710 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {1, 8, 9} → False := by
  intro a306 n10 n64
  have hc := h.complementary {3, 5, 6, 7} {0, 2, 4} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n64)

theorem c27718 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 4, 9} → ¬ T {1, 2, 8} → False := by
  intro a306 n26 n42
  have hc := h.complementary {3, 5, 6, 7} {0, 4, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n42)

theorem c27720 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 8, 9} → ¬ T {1, 2, 4} → False := by
  intro a306 n36 n38
  have hc := h.complementary {3, 5, 6, 7} {0, 8, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n36 (hc.mpr n38)

theorem c27721 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 8, 9} → T {1, 2, 4} → False := by
  intro a306 a36 a38
  have hc := h.complementary {3, 5, 6, 7} {0, 8, 9} a306 (by decide) (by decide)
  have he : ( {3, 5, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a36 a38

theorem c27765 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a306 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 7} {1, 2} {0, 4, 9} a306 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27827 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → T {0, 4, 9} → T {1, 4, 9} → T {2, 4, 9} → False := by
  intro a306 a26 a54 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 7} {4, 9} {0, 1, 2} a306 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)

theorem c27838 (h : TenSystem T Q) :
    Q {3, 5, 6, 7} → ¬ T {0, 8, 9} → ¬ T {2, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a306 n36 n85 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 7} {8, 9} {0, 2, 4} a306 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n36 (Eq.mp (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) ht)
  · exact n85 (Eq.mp (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c27843 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {4, 7, 9} → False := by
  intro a307 a1 a109
  have hc := h.complementary {3, 5, 6, 8} {0, 1, 2} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a109

theorem c27849 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 9} → T {2, 4, 7} → False := by
  intro a307 a8 a73
  have hc := h.complementary {3, 5, 6, 8} {0, 1, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a73

theorem c27854 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 2, 9} → ¬ T {1, 4, 7} → False := by
  intro a307 n15 n52
  have hc := h.complementary {3, 5, 6, 8} {0, 2, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 7} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n52)

theorem c27855 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {1, 4, 7} → False := by
  intro a307 a15 a52
  have hc := h.complementary {3, 5, 6, 8} {0, 2, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a52

theorem c27856 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 2, 9} → False := by
  intro a307 n24 n43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n43)

theorem c27857 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 7} → T {1, 2, 9} → False := by
  intro a307 a24 a43
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 7} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a43

theorem c27858 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 9} → ¬ T {1, 2, 7} → False := by
  intro a307 n26 n41
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n41)

theorem c27859 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 9} → T {1, 2, 7} → False := by
  intro a307 a26 a41
  have hc := h.complementary {3, 5, 6, 8} {0, 4, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a26 a41

theorem c27860 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 4} → False := by
  intro a307 n35 n38
  have hc := h.complementary {3, 5, 6, 8} {0, 7, 9} a307 (by decide) (by decide)
  have he : ( {3, 5, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n38)

theorem c27863 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a307 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 1} {2, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c27865 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 9} → False := by
  intro a307 a1 a3 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 1} {2, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c27871 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a307 a1 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 2} {1, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

end BorsukNine.FiniteObstruction

end OAI
