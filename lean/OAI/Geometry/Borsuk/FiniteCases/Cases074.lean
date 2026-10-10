import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28768 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 1, 8} → ¬ T {1, 2, 8} → ¬ T {1, 5, 8} → False := by
  intro a313 n7 n42 n57
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {1, 8} {0, 2, 5} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 8} = {0, 1, 8} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 8} = {1, 2, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) ht)

theorem c28776 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {1, 2, 4} → ¬ T {2, 4, 8} → False := by
  intro a313 n10 n38 n74
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {2, 4} {0, 1, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 4} = {2, 4, 8} by decide)) ht)

theorem c28781 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {1, 2, 4} → T {2, 4, 5} → T {2, 4, 8} → False := by
  intro a313 a38 a71 a74
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {2, 4} {1, 5, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 4} = {2, 4, 8} by decide)) a74)

theorem c28799 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 4, 5} → T {1, 4, 5} → T {2, 4, 5} → False := by
  intro a313 a22 a50 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {4, 5} {0, 1, 2} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)

theorem c28800 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {1, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n22 n50 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {0, 1, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28802 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n22 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {0, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28804 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {1, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a313 n50 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {4, 5} {1, 2, 8} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c28815 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → T {0, 5, 8} → T {1, 5, 8} → T {2, 5, 8} → False := by
  intro a313 a29 a57 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 7, 9} {5, 8} {0, 1, 2} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)

theorem c28816 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a313 n29 n57 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {5, 8} {0, 1, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c28818 (h : TenSystem T Q) :
    Q {3, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a313 n29 n78 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 7, 9} {5, 8} {0, 2, 4} a313 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c28823 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {4, 5, 7} → False := by
  intro a314 a1 a102
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 2} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a102

theorem c28826 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 7} → False := by
  intro a314 n4 n73
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n73)

theorem c28829 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 7} → T {2, 4, 5} → False := by
  intro a314 a6 a71
  have hc := h.complementary {3, 6, 8, 9} {0, 1, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a6 a71

theorem c28830 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {1, 5, 7} → False := by
  intro a314 n10 n56
  have hc := h.complementary {3, 6, 8, 9} {0, 2, 4} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n56)

theorem c28836 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 7} → False := by
  intro a314 n22 n41
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n41)

theorem c28837 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 4, 5} → T {1, 2, 7} → False := by
  intro a314 a22 a41
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 5} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a22 a41

theorem c28838 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 2, 5} → False := by
  intro a314 n24 n39
  have hc := h.complementary {3, 6, 8, 9} {0, 4, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n39)

theorem c28840 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 5, 7} → ¬ T {1, 2, 4} → False := by
  intro a314 n28 n38
  have hc := h.complementary {3, 6, 8, 9} {0, 5, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n38)

theorem c28841 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 5, 7} → T {1, 2, 4} → False := by
  intro a314 a28 a38
  have hc := h.complementary {3, 6, 8, 9} {0, 5, 7} a314 (by decide) (by decide)
  have he : ( {3, 6, 8, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a28 a38

theorem c28845 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a314 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {0, 1} {2, 4, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c28853 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a314 a1 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {0, 2} {1, 4, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c28855 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a314 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {0, 2} {1, 5, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c28887 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a314 a1 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {1, 2} {0, 5, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c28891 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 1, 4} → T {1, 2, 4} → T {1, 4, 5} → False := by
  intro a314 a3 a38 a50
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {1, 4} {0, 2, 5} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)

theorem c28924 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → ¬ T {0, 2, 5} → ¬ T {1, 2, 5} → ¬ T {2, 5, 7} → False := by
  intro a314 n11 n39 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 6, 8, 9} {2, 5} {0, 1, 7} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 5} = {0, 2, 5} by decide)) ht)
  · exact n39 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) ht)

theorem c28931 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 2, 7} → T {1, 2, 7} → T {2, 4, 7} → False := by
  intro a314 a13 a41 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {2, 7} {0, 1, 4} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 7} = {2, 4, 7} by decide)) a73)

theorem c28947 (h : TenSystem T Q) :
    Q {3, 6, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {2, 4, 7} → False := by
  intro a314 a24 a52 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 6, 8, 9} {4, 7} {0, 1, 2} a314 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)

theorem c28963 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {4, 5, 6} → False := by
  intro a315 a1 a101
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 2} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a1 a101

theorem c28964 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {2, 5, 6} → False := by
  intro a315 n3 n76
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n76)

theorem c28965 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 4} → T {2, 5, 6} → False := by
  intro a315 a3 a76
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a3 a76

theorem c28966 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 5} → ¬ T {2, 4, 6} → False := by
  intro a315 n4 n72
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 5} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n72)

theorem c28968 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 6} → ¬ T {2, 4, 5} → False := by
  intro a315 n5 n71
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 5} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n71)

theorem c28969 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 6} → T {2, 4, 5} → False := by
  intro a315 a5 a71
  have hc := h.complementary {3, 7, 8, 9} {0, 1, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a5 a71

theorem c28971 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 4} → T {1, 5, 6} → False := by
  intro a315 a10 a55
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 4} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a10 a55

theorem c28972 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 2, 5} → ¬ T {1, 4, 6} → False := by
  intro a315 n11 n51
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 5} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n51)

theorem c28975 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 2, 6} → T {1, 4, 5} → False := by
  intro a315 a12 a50
  have hc := h.complementary {3, 7, 8, 9} {0, 2, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a12 a50

theorem c28976 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 2, 6} → False := by
  intro a315 n22 n40
  have hc := h.complementary {3, 7, 8, 9} {0, 4, 5} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n40)

theorem c28978 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 4, 6} → ¬ T {1, 2, 5} → False := by
  intro a315 n23 n39
  have hc := h.complementary {3, 7, 8, 9} {0, 4, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n39)

theorem c28980 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 5, 6} → ¬ T {1, 2, 4} → False := by
  intro a315 n27 n38
  have hc := h.complementary {3, 7, 8, 9} {0, 5, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n38)

theorem c28981 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 5, 6} → T {1, 2, 4} → False := by
  intro a315 a27 a38
  have hc := h.complementary {3, 7, 8, 9} {0, 5, 6} a315 (by decide) (by decide)
  have he : ( {3, 7, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a27 a38

theorem c28983 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 5} → False := by
  intro a315 a1 a3 a4
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 1} {2, 4, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)

theorem c28985 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a315 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 1} {2, 4, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28988 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 5} → ¬ T {0, 1, 6} → False := by
  intro a315 n3 n4 n5
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 1} {4, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n4 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)

theorem c28995 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 6} → False := by
  intro a315 a1 a11 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 2} {1, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c28998 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 2, 4} → ¬ T {0, 4, 5} → False := by
  intro a315 n3 n10 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 4} {1, 2, 5} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c29001 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → T {0, 1, 4} → T {0, 2, 4} → T {0, 4, 6} → False := by
  intro a315 a3 a10 a23
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 7, 8, 9} {0, 4} {1, 2, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)

theorem c29002 (h : TenSystem T Q) :
    Q {3, 7, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 6} → False := by
  intro a315 n3 n22 n23
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 7, 8, 9} {0, 4} {1, 5, 6} a315 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
