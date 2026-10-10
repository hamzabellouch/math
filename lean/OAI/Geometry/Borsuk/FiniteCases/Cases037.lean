import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c10366 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {1, 2, 4} → ¬ T {1, 2, 6} → ¬ T {1, 2, 9} → False := by
  intro a182 n38 n40 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 7, 8} {1, 2} {4, 6, 9} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

theorem c10379 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a182 a39 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {1, 5} {2, 4, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c10411 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a182 a39 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {2, 5} {1, 4, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c10421 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 6} → T {2, 4, 6} → T {2, 6, 9} → False := by
  intro a182 a40 a72 a82
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {2, 6} {1, 4, 9} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) a82)

theorem c10435 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a182 a50 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {4, 5} {1, 2, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c10455 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 4, 9} → T {4, 5, 9} → T {4, 6, 9} → False := by
  intro a182 a54 a104 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 8} {4, 9} {1, 5, 6} a182 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)

theorem c10482 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a183 n38 n112
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 4} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n112)

theorem c10484 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a183 n39 n106
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 5} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n106)

theorem c10485 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 2, 5} → T {4, 6, 8} → False := by
  intro a183 a39 a106
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 5} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a39 a106

theorem c10486 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 2, 6} → ¬ T {4, 5, 8} → False := by
  intro a183 n40 n103
  have hc := h.complementary {0, 3, 7, 9} {1, 2, 6} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n103)

theorem c10493 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 4, 6} → T {2, 5, 8} → False := by
  intro a183 a51 a78
  have hc := h.complementary {0, 3, 7, 9} {1, 4, 6} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a51 a78

theorem c10499 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 5, 8} → T {2, 4, 6} → False := by
  intro a183 a57 a72
  have hc := h.complementary {0, 3, 7, 9} {1, 5, 8} a183 (by decide) (by decide)
  have he : ( {0, 3, 7, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a57 a72

theorem c10519 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 2, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a183 a39 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {1, 5} {2, 4, 6} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c10583 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 4, 6} → T {2, 4, 6} → T {4, 5, 6} → False := by
  intro a183 a51 a72 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {4, 6} {1, 2, 5} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)

theorem c10585 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 4, 6} → T {2, 4, 6} → T {4, 6, 8} → False := by
  intro a183 a51 a72 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {4, 6} {1, 2, 8} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c10587 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a183 a51 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 7, 9} {4, 6} {1, 5, 8} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c10608 (h : TenSystem T Q) :
    Q {0, 3, 7, 9} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a183 n57 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 7, 9} {5, 8} {1, 2, 6} a183 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c10623 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 4} → T {5, 6, 7} → False := by
  intro a184 a38 a111
  have hc := h.complementary {0, 3, 8, 9} {1, 2, 4} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a38 a111

theorem c10626 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 2, 6} → ¬ T {4, 5, 7} → False := by
  intro a184 n40 n102
  have hc := h.complementary {0, 3, 8, 9} {1, 2, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n102)

theorem c10627 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 6} → T {4, 5, 7} → False := by
  intro a184 a40 a102
  have hc := h.complementary {0, 3, 8, 9} {1, 2, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a40 a102

theorem c10635 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 7} → T {2, 5, 6} → False := by
  intro a184 a52 a76
  have hc := h.complementary {0, 3, 8, 9} {1, 4, 7} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a52 a76

theorem c10636 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 5, 6} → ¬ T {2, 4, 7} → False := by
  intro a184 n55 n73
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n55 (hc.mpr n73)

theorem c10637 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 6} → T {2, 4, 7} → False := by
  intro a184 a55 a73
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 6} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a55 a73

theorem c10638 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 5, 7} → ¬ T {2, 4, 6} → False := by
  intro a184 n56 n72
  have hc := h.complementary {0, 3, 8, 9} {1, 5, 7} a184 (by decide) (by decide)
  have he : ( {0, 3, 8, 9} : Finset Labels)ᶜ \ {1, 5, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n72)

theorem c10691 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 6} → False := by
  intro a184 a39 a71 a76
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {2, 5} {1, 4, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)

theorem c10693 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 2, 5} → T {2, 4, 5} → T {2, 5, 7} → False := by
  intro a184 a39 a71 a77
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {2, 5} {1, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) a77)

theorem c10715 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a184 a50 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 2, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c10717 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a184 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 2, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10718 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {1, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → False := by
  intro a184 n50 n101 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 8, 9} {4, 5} {1, 6, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n50 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)

theorem c10719 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a184 a50 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 5} {1, 6, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10725 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a184 a51 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 6} {1, 2, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c10727 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a184 a51 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {4, 6} {1, 5, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c10743 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 6} → T {4, 5, 6} → T {5, 6, 7} → False := by
  intro a184 a55 a101 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {5, 6} {1, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c10744 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a184 n76 n101 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 8, 9} {5, 6} {2, 4, 7} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c10751 (h : TenSystem T Q) :
    Q {0, 3, 8, 9} → T {1, 5, 7} → T {4, 5, 7} → T {5, 6, 7} → False := by
  intro a184 a56 a102 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 8, 9} {5, 7} {1, 4, 6} a184 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)

theorem c10763 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {7, 8, 9} → False := by
  intro a185 a37 a120
  have hc := h.complementary {0, 4, 5, 6} {1, 2, 3} a185 (by decide) (by decide)
  have he : ( {0, 4, 5, 6} : Finset Labels)ᶜ \ {1, 2, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a120

theorem c10778 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {1, 7, 9} → ¬ T {2, 3, 8} → False := by
  intro a185 n63 n69
  have hc := h.complementary {0, 4, 5, 6} {1, 7, 9} a185 (by decide) (by decide)
  have he : ( {0, 4, 5, 6} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 3, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n69)

theorem c10780 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {1, 8, 9} → ¬ T {2, 3, 7} → False := by
  intro a185 n64 n68
  have hc := h.complementary {0, 4, 5, 6} {1, 8, 9} a185 (by decide) (by decide)
  have he : ( {0, 4, 5, 6} : Finset Labels)ᶜ \ {1, 8, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n64 (hc.mpr n68)

theorem c10785 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a185 a37 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 2} {3, 7, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c10793 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a185 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 3} {2, 7, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c10795 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a185 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 3} {2, 8, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c10817 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 9} → T {1, 3, 9} → T {1, 8, 9} → False := by
  intro a185 a43 a49 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {1, 9} {2, 3, 8} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c10827 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a185 a37 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 3} {1, 8, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c10833 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 7} → T {2, 3, 7} → T {2, 7, 9} → False := by
  intro a185 a41 a68 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 7} {1, 3, 9} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) a84)

theorem c10849 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 9} → T {2, 3, 9} → T {2, 8, 9} → False := by
  intro a185 a43 a70 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 9} {1, 3, 8} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c10851 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → T {1, 2, 9} → T {2, 7, 9} → T {2, 8, 9} → False := by
  intro a185 a43 a84 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 6} {2, 9} {1, 7, 8} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

end BorsukNine.FiniteObstruction

end OAI
