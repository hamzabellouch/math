import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c26087 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a294 a2 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {1, 3} {0, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c26103 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a294 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {1, 5} {0, 4, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c26121 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {1, 3, 4} → T {3, 4, 5} → T {3, 4, 7} → False := by
  intro a294 a44 a86 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {3, 4} {1, 5, 7} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)

theorem c26139 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 4, 5} → T {1, 4, 5} → T {3, 4, 5} → False := by
  intro a294 a22 a50 a86
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {4, 5} {0, 1, 3} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)

theorem c26147 (h : TenSystem T Q) :
    Q {2, 6, 8, 9} → T {0, 4, 7} → T {1, 4, 7} → T {3, 4, 7} → False := by
  intro a294 a24 a52 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 6, 8, 9} {4, 7} {0, 1, 3} a294 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c26168 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {0, 1, 6} → ¬ T {3, 4, 5} → False := by
  intro a295 n5 n86
  have hc := h.complementary {2, 7, 8, 9} {0, 1, 6} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 4, 5} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n86)

theorem c26172 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → ¬ T {0, 3, 5} → ¬ T {1, 4, 6} → False := by
  intro a295 n17 n51
  have hc := h.complementary {2, 7, 8, 9} {0, 3, 5} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n51)

theorem c26175 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 3, 6} → T {1, 4, 5} → False := by
  intro a295 a18 a50
  have hc := h.complementary {2, 7, 8, 9} {0, 3, 6} a295 (by decide) (by decide)
  have he : ( {2, 7, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a18 a50

theorem c26227 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a295 a2 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {1, 3} {0, 5, 6} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c26259 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 3, 4} → T {3, 4, 5} → T {3, 4, 6} → False := by
  intro a295 a16 a86 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {3, 4} {0, 5, 6} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)

theorem c26287 (h : TenSystem T Q) :
    Q {2, 7, 8, 9} → T {0, 4, 6} → T {1, 4, 6} → T {3, 4, 6} → False := by
  intro a295 a23 a51 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 7, 8, 9} {4, 6} {0, 1, 3} a295 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c26303 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {7, 8, 9} → False := by
  intro a296 a1 a120
  have hc := h.complementary {3, 4, 5, 6} {0, 1, 2} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 1, 2} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a120

theorem c26310 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 2, 7} → ¬ T {1, 8, 9} → False := by
  intro a296 n13 n64
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 7} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n64)

theorem c26311 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 2, 7} → T {1, 8, 9} → False := by
  intro a296 a13 a64
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 7} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a64

theorem c26312 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 2, 8} → ¬ T {1, 7, 9} → False := by
  intro a296 n14 n63
  have hc := h.complementary {3, 4, 5, 6} {0, 2, 8} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 7, 9} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n63)

theorem c26317 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 7, 8} → T {1, 2, 9} → False := by
  intro a296 a34 a43
  have hc := h.complementary {3, 4, 5, 6} {0, 7, 8} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 8} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a34 a43

theorem c26318 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 7, 9} → ¬ T {1, 2, 8} → False := by
  intro a296 n35 n42
  have hc := h.complementary {3, 4, 5, 6} {0, 7, 9} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 8} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n42)

theorem c26320 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 8, 9} → ¬ T {1, 2, 7} → False := by
  intro a296 n36 n41
  have hc := h.complementary {3, 4, 5, 6} {0, 8, 9} a296 (by decide) (by decide)
  have he : ( {3, 4, 5, 6} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n36 (hc.mpr n41)

theorem c26331 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a296 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {0, 2} {1, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c26363 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 8} → False := by
  intro a296 a1 a41 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {1, 2} {0, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c26365 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a296 a1 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {1, 2} {0, 7, 9} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26374 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → ¬ T {0, 1, 7} → ¬ T {1, 7, 8} → ¬ T {1, 7, 9} → False := by
  intro a296 n6 n62 n63
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 6} {1, 7} {0, 8, 9} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n6 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 7} = {0, 1, 7} by decide)) ht)
  · exact n62 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) ht)
  · exact n63 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) ht)

theorem c26391 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {0, 1, 9} → T {1, 7, 9} → T {1, 8, 9} → False := by
  intro a296 a8 a63 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {1, 9} {0, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c26417 (h : TenSystem T Q) :
    Q {3, 4, 5, 6} → T {1, 2, 9} → T {2, 7, 9} → T {2, 8, 9} → False := by
  intro a296 a43 a84 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 6} {2, 9} {1, 7, 8} a296 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c26450 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {0, 2, 6} → ¬ T {1, 8, 9} → False := by
  intro a297 n12 n64
  have hc := h.complementary {3, 4, 5, 7} {0, 2, 6} a297 (by decide) (by decide)
  have he : ( {3, 4, 5, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n64)

theorem c26471 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a297 a1 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {0, 2} {1, 6, 8} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c26473 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a297 a1 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {0, 2} {1, 6, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c26480 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 9} → False := by
  intro a297 n5 n12 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 7} {0, 6} {1, 2, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c26497 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 9} → T {0, 2, 9} → T {0, 8, 9} → False := by
  intro a297 a8 a15 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {0, 9} {1, 2, 8} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c26505 (h : TenSystem T Q) :
    Q {3, 4, 5, 7} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a297 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 7} {1, 2} {0, 6, 9} a297 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26583 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {6, 7, 9} → False := by
  intro a298 a1 a118
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 2} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 2} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a1 a118

theorem c26585 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 6} → T {2, 7, 9} → False := by
  intro a298 a5 a84
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 6} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a5 a84

theorem c26587 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 7} → T {2, 6, 9} → False := by
  intro a298 a6 a82
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 7} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a82

theorem c26589 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 9} → T {2, 6, 7} → False := by
  intro a298 a8 a80
  have hc := h.complementary {3, 4, 5, 8} {0, 1, 9} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a80

theorem c26597 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 6, 7} → T {1, 2, 9} → False := by
  intro a298 a31 a43
  have hc := h.complementary {3, 4, 5, 8} {0, 6, 7} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 9} := by decide
  rw [he] at hc
  exact hc.mp a31 a43

theorem c26600 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {0, 7, 9} → ¬ T {1, 2, 6} → False := by
  intro a298 n35 n40
  have hc := h.complementary {3, 4, 5, 8} {0, 7, 9} a298 (by decide) (by decide)
  have he : ( {3, 4, 5, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n40)

theorem c26605 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 9} → False := by
  intro a298 a1 a5 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {0, 1} {2, 6, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c26611 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a298 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {0, 2} {1, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c26643 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a298 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 2} {0, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c26645 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a298 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 2} {0, 6, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26647 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 2} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a298 a1 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 2} {0, 7, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c26666 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {0, 1, 9} → ¬ T {1, 2, 9} → ¬ T {1, 6, 9} → False := by
  intro a298 n8 n43 n61
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 8} {1, 9} {0, 2, 6} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n61 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) ht)

theorem c26671 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 1, 9} → T {1, 6, 9} → T {1, 7, 9} → False := by
  intro a298 a8 a61 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {1, 9} {0, 6, 7} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c26682 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {1, 2, 7} → ¬ T {2, 6, 7} → False := by
  intro a298 n13 n41 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 8} {2, 7} {0, 1, 6} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c26704 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → ¬ T {1, 6, 7} → ¬ T {2, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a298 n59 n80 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 5, 8} {6, 7} {1, 2, 9} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c26715 (h : TenSystem T Q) :
    Q {3, 4, 5, 8} → T {0, 7, 9} → T {1, 7, 9} → T {2, 7, 9} → False := by
  intro a298 a35 a63 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 5, 8} {7, 9} {0, 1, 2} a298 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)

end BorsukNine.FiniteObstruction

end OAI
