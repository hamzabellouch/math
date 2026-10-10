import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c26723 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {6, 7, 8} → False := by
  intro a299 a1 a117
  have hc := h.complementary {3, 4, 5, 9} {0, 1, 2} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a117

theorem c26731 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 2, 6} → T {1, 7, 8} → False := by
  intro a299 a12 a62
  have hc := h.complementary {3, 4, 5, 9} {0, 2, 6} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a62

theorem c26736 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 8} → False := by
  intro a299 n31 n42
  have hc := h.complementary {3, 4, 5, 9} {0, 6, 7} a299 (by decide) (by decide)
  have he : ( {3, 4, 5, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n42)

theorem c26743 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 7} → False := by
  intro a299 a1 a5 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {0, 1} {2, 6, 7} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c26751 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a299 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {0, 2} {1, 6, 7} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c26755 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a299 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {0, 2} {1, 7, 8} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c26783 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a299 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {1, 2} {0, 6, 7} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c26785 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a299 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {1, 2} {0, 6, 8} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c26787 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 8} → False := by
  intro a299 a1 a41 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {1, 2} {0, 7, 8} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c26839 (h : TenSystem T Q) :
    Q {3, 4, 5, 9} → T {0, 6, 7} → T {1, 6, 7} → T {2, 6, 7} → False := by
  intro a299 a31 a59 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 9} {6, 7} {0, 1, 2} a299 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)

theorem c26863 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {5, 8, 9} → False := by
  intro a300 a1 a116
  have hc := h.complementary {3, 4, 6, 7} {0, 1, 2} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a116

theorem c26869 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 9} → T {2, 5, 8} → False := by
  intro a300 a8 a78
  have hc := h.complementary {3, 4, 6, 7} {0, 1, 9} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a8 a78

theorem c26870 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 2, 5} → ¬ T {1, 8, 9} → False := by
  intro a300 n11 n64
  have hc := h.complementary {3, 4, 6, 7} {0, 2, 5} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n64)

theorem c26871 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 2, 5} → T {1, 8, 9} → False := by
  intro a300 a11 a64
  have hc := h.complementary {3, 4, 6, 7} {0, 2, 5} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a11 a64

theorem c26875 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 2, 9} → T {1, 5, 8} → False := by
  intro a300 a15 a57
  have hc := h.complementary {3, 4, 6, 7} {0, 2, 9} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a57

theorem c26876 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 2, 9} → False := by
  intro a300 n29 n43
  have hc := h.complementary {3, 4, 6, 7} {0, 5, 8} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n43)

theorem c26877 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 5, 8} → T {1, 2, 9} → False := by
  intro a300 a29 a43
  have hc := h.complementary {3, 4, 6, 7} {0, 5, 8} a300 (by decide) (by decide)
  have he : ( {3, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a43

theorem c26891 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a300 a1 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 2} {1, 5, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c26893 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 9} → False := by
  intro a300 a1 a11 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 2} {1, 5, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c26896 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 2, 5} → ¬ T {0, 2, 8} → ¬ T {0, 2, 9} → False := by
  intro a300 n11 n14 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {0, 2} {5, 8, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c26899 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 5} → T {0, 2, 5} → T {0, 5, 8} → False := by
  intro a300 a4 a11 a29
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 5} {1, 2, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 5} = {0, 5, 8} by decide)) a29)

theorem c26905 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 2, 5} → T {0, 5, 8} → T {0, 5, 9} → False := by
  intro a300 a11 a29 a30
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 5} {2, 8, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 5} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 5} = {0, 5, 9} by decide)) a30)

theorem c26913 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 2, 8} → T {0, 5, 8} → T {0, 8, 9} → False := by
  intro a300 a14 a29 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {0, 8} {2, 5, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 8} = {0, 8, 9} by decide)) a36)

theorem c26914 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {0, 2, 9} → ¬ T {0, 5, 9} → False := by
  intro a300 n8 n15 n30
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {0, 9} {1, 2, 5} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) ht)
  · exact n30 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) ht)

theorem c26916 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {0, 2, 9} → ¬ T {0, 8, 9} → False := by
  intro a300 n8 n15 n36
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {0, 9} {1, 2, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) ht)
  · exact n36 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) ht)

theorem c26925 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a300 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {1, 2} {0, 5, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26927 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 1, 2} → T {1, 2, 8} → T {1, 2, 9} → False := by
  intro a300 a1 a42 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {1, 2} {0, 8, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26948 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {1, 2, 9} → ¬ T {1, 8, 9} → False := by
  intro a300 n8 n43 n64
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {1, 9} {0, 2, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) ht)

theorem c26952 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {1, 2, 9} → ¬ T {1, 5, 9} → ¬ T {1, 8, 9} → False := by
  intro a300 n43 n58 n64
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {1, 9} {2, 5, 8} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) ht)

theorem c26979 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → T {0, 5, 8} → T {1, 5, 8} → T {2, 5, 8} → False := by
  intro a300 a29 a57 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 7} {5, 8} {0, 1, 2} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)

theorem c26980 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a300 n29 n57 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {5, 8} {0, 1, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c26982 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a300 n29 n78 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {5, 8} {0, 2, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c26984 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a300 n57 n78 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {5, 8} {1, 2, 9} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c26996 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {0, 8, 9} → ¬ T {1, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a300 n36 n64 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {8, 9} {0, 1, 5} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n36 (Eq.mp (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c27000 (h : TenSystem T Q) :
    Q {3, 4, 6, 7} → ¬ T {1, 8, 9} → ¬ T {2, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a300 n64 n85 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 7} {8, 9} {1, 2, 5} a300 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n85 (Eq.mp (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c27012 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 2, 7} → ¬ T {1, 5, 9} → False := by
  intro a301 n13 n58
  have hc := h.complementary {3, 4, 6, 8} {0, 2, 7} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n58)

theorem c27013 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 2, 7} → T {1, 5, 9} → False := by
  intro a301 a13 a58
  have hc := h.complementary {3, 4, 6, 8} {0, 2, 7} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a58

theorem c27017 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 5, 7} → T {1, 2, 9} → False := by
  intro a301 a28 a43
  have hc := h.complementary {3, 4, 6, 8} {0, 5, 7} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a43

theorem c27020 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 5} → False := by
  intro a301 n35 n39
  have hc := h.complementary {3, 4, 6, 8} {0, 7, 9} a301 (by decide) (by decide)
  have he : ( {3, 4, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n39)

theorem c27025 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {0, 1, 5} → T {0, 1, 9} → False := by
  intro a301 a1 a4 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {0, 1} {2, 5, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c27031 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a301 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {0, 2} {1, 5, 7} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27063 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a301 a1 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 5, 7} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c27065 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a301 a1 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 5, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27067 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a301 a1 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {1, 2} {0, 7, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27102 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 2, 7} → ¬ T {1, 2, 7} → ¬ T {2, 5, 7} → False := by
  intro a301 n13 n41 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 8} {2, 7} {0, 1, 5} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
