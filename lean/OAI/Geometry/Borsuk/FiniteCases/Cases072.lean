import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c28213 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {1, 2, 9} → T {1, 4, 9} → T {1, 6, 9} → False := by
  intro a309 a43 a54 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {1, 9} {2, 4, 6} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) a61)

theorem c28239 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → T {0, 4, 6} → T {1, 4, 6} → T {2, 4, 6} → False := by
  intro a309 a23 a51 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 8} {4, 6} {0, 1, 2} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)

theorem c28240 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {1, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n23 n51 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {0, 1, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28242 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {2, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n23 n72 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {0, 2, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28244 (h : TenSystem T Q) :
    Q {3, 5, 7, 8} → ¬ T {1, 4, 6} → ¬ T {2, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a309 n51 n72 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 7, 8} {4, 6} {1, 2, 9} a309 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c28263 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {4, 6, 8} → False := by
  intro a310 a1 a106
  have hc := h.complementary {3, 5, 7, 9} {0, 1, 2} a310 (by decide) (by decide)
  have he : ( {3, 5, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a106

theorem c28274 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {0, 2, 8} → ¬ T {1, 4, 6} → False := by
  intro a310 n14 n51
  have hc := h.complementary {3, 5, 7, 9} {0, 2, 8} a310 (by decide) (by decide)
  have he : ( {3, 5, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n51)

theorem c28278 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → ¬ T {0, 4, 8} → ¬ T {1, 2, 6} → False := by
  intro a310 n25 n40
  have hc := h.complementary {3, 5, 7, 9} {0, 4, 8} a310 (by decide) (by decide)
  have he : ( {3, 5, 7, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n40)

theorem c28291 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 6} → False := by
  intro a310 a1 a10 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {0, 2} {1, 4, 6} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c28295 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a310 a1 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {0, 2} {1, 6, 8} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c28327 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a310 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {1, 2} {0, 6, 8} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c28355 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 2, 4} → T {1, 2, 4} → T {2, 4, 6} → False := by
  intro a310 a10 a38 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {2, 4} {0, 1, 6} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c28379 (h : TenSystem T Q) :
    Q {3, 5, 7, 9} → T {0, 4, 6} → T {1, 4, 6} → T {2, 4, 6} → False := by
  intro a310 a23 a51 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 7, 9} {4, 6} {0, 1, 2} a310 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)

theorem c28403 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {4, 6, 7} → False := by
  intro a311 a1 a105
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 2} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a1 a105

theorem c28404 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 1, 4} → ¬ T {2, 6, 7} → False := by
  intro a311 n3 n80
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 4} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n80)

theorem c28405 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 4} → T {2, 6, 7} → False := by
  intro a311 a3 a80
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 4} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a3 a80

theorem c28407 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 6} → T {2, 4, 7} → False := by
  intro a311 a5 a73
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a5 a73

theorem c28408 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 1, 7} → ¬ T {2, 4, 6} → False := by
  intro a311 n6 n72
  have hc := h.complementary {3, 5, 8, 9} {0, 1, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n72)

theorem c28411 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 4} → T {1, 6, 7} → False := by
  intro a311 a10 a59
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 4} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {1, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a10 a59

theorem c28412 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 4, 7} → False := by
  intro a311 n12 n52
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n52)

theorem c28413 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 6} → T {1, 4, 7} → False := by
  intro a311 a12 a52
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a52

theorem c28414 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 7} → ¬ T {1, 4, 6} → False := by
  intro a311 n13 n51
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n51)

theorem c28415 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 7} → T {1, 4, 6} → False := by
  intro a311 a13 a51
  have hc := h.complementary {3, 5, 8, 9} {0, 2, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a51

theorem c28416 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 6} → ¬ T {1, 2, 7} → False := by
  intro a311 n23 n41
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n41)

theorem c28417 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 4, 6} → T {1, 2, 7} → False := by
  intro a311 a23 a41
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 6} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a23 a41

theorem c28418 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 2, 6} → False := by
  intro a311 n24 n40
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n40)

theorem c28419 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 4, 7} → T {1, 2, 6} → False := by
  intro a311 a24 a40
  have hc := h.complementary {3, 5, 8, 9} {0, 4, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 2, 6} := by decide
  rw [he] at hc
  exact hc.mp a24 a40

theorem c28420 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 2, 4} → False := by
  intro a311 n31 n38
  have hc := h.complementary {3, 5, 8, 9} {0, 6, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n38)

theorem c28421 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 6, 7} → T {1, 2, 4} → False := by
  intro a311 a31 a38
  have hc := h.complementary {3, 5, 8, 9} {0, 6, 7} a311 (by decide) (by decide)
  have he : ( {3, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 2, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a38

theorem c28423 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 6} → False := by
  intro a311 a1 a3 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 1} {2, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c28425 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 1, 4} → T {0, 1, 7} → False := by
  intro a311 a1 a3 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 1} {2, 4, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c28428 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a311 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {0, 1} {4, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c28431 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 2, 4} → T {0, 2, 6} → False := by
  intro a311 a1 a10 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 2} {1, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c28435 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a311 a1 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 2} {1, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c28436 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 4} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a311 n10 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {0, 2} {4, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c28443 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a311 a3 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 4} {1, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c28445 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a311 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 4} {2, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c28459 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 7} → T {0, 4, 7} → T {0, 6, 7} → False := by
  intro a311 a6 a24 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 7} {1, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) a6)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c28461 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 7} → T {0, 4, 7} → T {0, 6, 7} → False := by
  intro a311 a13 a24 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {0, 7} {2, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c28463 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 6} → False := by
  intro a311 a1 a38 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 4, 6} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c28465 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 4} → T {1, 2, 7} → False := by
  intro a311 a1 a38 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 4, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c28467 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 7} → False := by
  intro a311 a1 a40 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {1, 2} {0, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c28468 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → False := by
  intro a311 n38 n40 n41
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {1, 2} {4, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)

theorem c28499 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → T {0, 2, 4} → T {2, 4, 6} → T {2, 4, 7} → False := by
  intro a311 a10 a72 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 5, 8, 9} {2, 4} {0, 6, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c28502 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 2, 6} → ¬ T {2, 4, 6} → False := by
  intro a311 n12 n40 n72
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {2, 6} {0, 1, 4} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)

theorem c28504 (h : TenSystem T Q) :
    Q {3, 5, 8, 9} → ¬ T {0, 2, 6} → ¬ T {1, 2, 6} → ¬ T {2, 6, 7} → False := by
  intro a311 n12 n40 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 5, 8, 9} {2, 6} {0, 1, 7} a311 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
