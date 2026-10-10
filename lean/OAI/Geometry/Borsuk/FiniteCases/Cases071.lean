import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c27873 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a307 a1 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 2} {1, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c27875 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 9} → False := by
  intro a307 a1 a13 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 2} {1, 7, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c27878 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 4, 7} → False := by
  intro a307 n3 n10 n24
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {0, 4} {1, 2, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) ht)

theorem c27901 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 7, 9} → False := by
  intro a307 a15 a26 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {0, 9} {2, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c27905 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a307 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 2} {0, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27907 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a307 a1 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 2} {0, 7, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27928 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 1, 9} → ¬ T {1, 2, 9} → ¬ T {1, 7, 9} → False := by
  intro a307 n8 n43 n63
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {1, 9} {0, 2, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n63 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) ht)

theorem c27931 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 1, 9} → T {1, 4, 9} → T {1, 7, 9} → False := by
  intro a307 a8 a54 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {1, 9} {0, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c27947 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 7} → T {2, 4, 7} → T {2, 7, 9} → False := by
  intro a307 a13 a73 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {2, 7} {0, 4, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) a84)

theorem c27950 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 2, 9} → ¬ T {1, 2, 9} → ¬ T {2, 4, 9} → False := by
  intro a307 n15 n43 n75
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {2, 9} {0, 1, 4} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)

theorem c27952 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 2, 9} → ¬ T {1, 2, 9} → ¬ T {2, 7, 9} → False := by
  intro a307 n15 n43 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {2, 9} {0, 1, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) ht)

theorem c27955 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 2, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a307 a15 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {2, 9} {0, 4, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c27959 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a307 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {4, 7} {0, 1, 2} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

theorem c27960 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a307 n24 n52 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {4, 7} {0, 1, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c27964 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {1, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a307 n52 n73 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {4, 7} {1, 2, 9} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c27967 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → T {0, 4, 9} → T {1, 4, 9} → T {2, 4, 9} → False := by
  intro a307 a26 a54 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 8} {4, 9} {0, 1, 2} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)

theorem c27970 (h : TenSystem T Q) :
    Q {3, 5, 6, 8} → ¬ T {0, 4, 9} → ¬ T {2, 4, 9} → ¬ T {4, 7, 9} → False := by
  intro a307 n26 n75 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 6, 8} {4, 9} {0, 2, 7} a307 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n26 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c27983 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {4, 7, 8} → False := by
  intro a308 a1 a108
  have hc := h.complementary {3, 5, 6, 9} {0, 1, 2} a308 (by decide) (by decide)
  have he : ( {3, 5, 6, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a108

theorem c28015 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a308 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {0, 2} {1, 7, 8} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c28047 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 8} → False := by
  intro a308 a1 a41 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {1, 2} {0, 7, 8} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28083 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 2, 7} → T {1, 2, 7} → T {2, 4, 7} → False := by
  intro a308 a13 a41 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {2, 7} {0, 1, 4} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)

theorem c28099 (h : TenSystem T Q) :
    Q {3, 5, 6, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a308 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 6, 9} {4, 7} {0, 1, 2} a308 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

theorem c28123 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {4, 6, 9} → False := by
  intro a309 a1 a107
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 2} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a107

theorem c28124 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 1, 4} → ¬ T {2, 6, 9} → False := by
  intro a309 n3 n82
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 6, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n82)

theorem c28128 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 1, 9} → ¬ T {2, 4, 6} → False := by
  intro a309 n8 n72
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n72)

theorem c28129 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 9} → T {2, 4, 6} → False := by
  intro a309 a8 a72
  have hc := h.complementary {3, 5, 7, 8} {0, 1, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a8 a72

theorem c28130 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {1, 6, 9} → False := by
  intro a309 n10 n61
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n61)

theorem c28131 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 2, 4} → T {1, 6, 9} → False := by
  intro a309 a10 a61
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 4} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a61

theorem c28134 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 9} → ¬ T {1, 4, 6} → False := by
  intro a309 n15 n51
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n51)

theorem c28135 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 2, 9} → T {1, 4, 6} → False := by
  intro a309 a15 a51
  have hc := h.complementary {3, 5, 7, 8} {0, 2, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a15 a51

theorem c28136 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {1, 2, 9} → False := by
  intro a309 n23 n43
  have hc := h.complementary {3, 5, 7, 8} {0, 4, 6} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n43)

theorem c28137 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 4, 6} → T {1, 2, 9} → False := by
  intro a309 a23 a43
  have hc := h.complementary {3, 5, 7, 8} {0, 4, 6} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a43

theorem c28140 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 6, 9} → ¬ T {1, 2, 4} → False := by
  intro a309 n33 n38
  have hc := h.complementary {3, 5, 7, 8} {0, 6, 9} a309 (by decide) (by decide)
  have he : ( {3, 5, 7, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n38)

theorem c28143 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a309 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 1} {2, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28153 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a309 a1 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 2} {1, 4, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c28156 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 6} → ¬ T {0, 2, 9} → False := by
  intro a309 n10 n12 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {0, 2} {4, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c28179 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a309 a8 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 9} {1, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c28181 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a309 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {0, 9} {2, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c28183 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a309 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 2} {0, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c28185 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a309 a1 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 2} {0, 4, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28187 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a309 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 2} {0, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c28191 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 4} → T {1, 2, 4} → T {1, 4, 6} → False := by
  intro a309 a3 a38 a51
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 4} {0, 2, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)

theorem c28195 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 1, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a309 a3 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 4} {0, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c28197 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {1, 2, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a309 a38 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 4} {2, 6, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c28208 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 1, 9} → ¬ T {1, 2, 9} → ¬ T {1, 6, 9} → False := by
  intro a309 n8 n43 n61
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {1, 9} {0, 2, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n61 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
