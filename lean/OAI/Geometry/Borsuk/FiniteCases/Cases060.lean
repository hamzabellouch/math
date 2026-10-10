import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c22090 (h : TenSystem T Q) :
    Q {2, 3, 4, 9} → ¬ T {0, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 7, 8} → False := by
  intro a265 n32 n112 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 4, 9} {6, 8} {0, 5, 7} a265 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)

theorem c22103 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 1, 4} → T {7, 8, 9} → False := by
  intro a266 a3 a120
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 4} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a120

theorem c22104 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 1, 7} → ¬ T {4, 8, 9} → False := by
  intro a266 n6 n110
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n110)

theorem c22105 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 1, 7} → T {4, 8, 9} → False := by
  intro a266 a6 a110
  have hc := h.complementary {2, 3, 5, 6} {0, 1, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a6 a110

theorem c22111 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {1, 8, 9} → False := by
  intro a266 a24 a64
  have hc := h.complementary {2, 3, 5, 6} {0, 4, 7} a266 (by decide) (by decide)
  have he : ( {2, 3, 5, 6} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a64

theorem c22193 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {1, 4, 9} → T {1, 7, 9} → T {1, 8, 9} → False := by
  intro a266 a54 a63 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {1, 9} {4, 7, 8} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c22196 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a266 n24 n52 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 6} {4, 7} {0, 1, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22197 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a266 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 7} {0, 1, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22198 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → ¬ T {0, 4, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a266 n24 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 6} {4, 7} {0, 8, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22199 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a266 a24 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 7} {0, 8, 9} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22215 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a266 a26 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {4, 9} {0, 7, 8} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c22231 (h : TenSystem T Q) :
    Q {2, 3, 5, 6} → T {0, 7, 9} → T {4, 7, 9} → T {7, 8, 9} → False := by
  intro a266 a35 a109 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 6} {7, 9} {0, 4, 8} a266 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c22242 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → ¬ T {0, 1, 4} → ¬ T {6, 8, 9} → False := by
  intro a267 n3 n119
  have hc := h.complementary {2, 3, 5, 7} {0, 1, 4} a267 (by decide) (by decide)
  have he : ( {2, 3, 5, 7} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n119)

theorem c22244 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → ¬ T {0, 1, 6} → ¬ T {4, 8, 9} → False := by
  intro a267 n5 n110
  have hc := h.complementary {2, 3, 5, 7} {0, 1, 6} a267 (by decide) (by decide)
  have he : ( {2, 3, 5, 7} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n110)

theorem c22357 (h : TenSystem T Q) :
    Q {2, 3, 5, 7} → T {1, 4, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a267 a54 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 7} {4, 9} {1, 6, 8} a267 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c22382 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 4} → ¬ T {6, 7, 9} → False := by
  intro a268 n3 n118
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 4} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n118)

theorem c22383 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 1, 4} → T {6, 7, 9} → False := by
  intro a268 a3 a118
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 4} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a118

theorem c22384 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 6} → ¬ T {4, 7, 9} → False := by
  intro a268 n5 n109
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 6} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n109)

theorem c22386 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 7} → ¬ T {4, 6, 9} → False := by
  intro a268 n6 n107
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 7} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n107)

theorem c22388 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 9} → ¬ T {4, 6, 7} → False := by
  intro a268 n8 n105
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 9} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n105)

theorem c22389 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 1, 9} → T {4, 6, 7} → False := by
  intro a268 a8 a105
  have hc := h.complementary {2, 3, 5, 8} {0, 1, 9} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a105

theorem c22393 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {1, 6, 9} → False := by
  intro a268 a24 a61
  have hc := h.complementary {2, 3, 5, 8} {0, 4, 7} a268 (by decide) (by decide)
  have he : ( {2, 3, 5, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a61

theorem c22402 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a268 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {0, 1} {4, 6, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c22423 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 1, 6} → T {0, 6, 7} → T {0, 6, 9} → False := by
  intro a268 a5 a31 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {0, 6} {1, 7, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) a33)

theorem c22451 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 1, 6} → T {1, 4, 6} → T {1, 6, 7} → False := by
  intro a268 a5 a51 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {1, 6} {0, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) a59)

theorem c22475 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a268 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {0, 1, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c22477 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 9} → False := by
  intro a268 a23 a51 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {0, 1, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c22478 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a268 n23 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {4, 6} {0, 7, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c22479 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a268 a23 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {0, 7, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c22481 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a268 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 6} {1, 7, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c22483 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {1, 4, 7} → T {4, 6, 7} → False := by
  intro a268 a24 a52 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 7} {0, 1, 6} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c22485 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a268 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 7} {0, 1, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22486 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a268 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {4, 7} {0, 6, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22487 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a268 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 7} {0, 6, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22494 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 4, 9} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → False := by
  intro a268 n26 n107 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {4, 9} {0, 6, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n26 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c22497 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a268 a54 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {4, 9} {1, 6, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c22502 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a268 n31 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 7} {0, 4, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c22503 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a268 a31 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {6, 7} {0, 4, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c22505 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a268 a59 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {6, 7} {1, 4, 9} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c22506 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 6, 9} → ¬ T {1, 6, 9} → ¬ T {4, 6, 9} → False := by
  intro a268 n33 n61 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 9} {0, 1, 4} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n61 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)

theorem c22510 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {0, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a268 n33 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 9} {0, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c22511 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {0, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a268 a33 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {6, 9} {0, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c22512 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → ¬ T {1, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a268 n61 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 8} {6, 9} {1, 4, 7} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n61 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c22521 (h : TenSystem T Q) :
    Q {2, 3, 5, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a268 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 8} {7, 9} {1, 4, 6} a268 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c22522 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 4} → ¬ T {6, 7, 8} → False := by
  intro a269 n3 n117
  have hc := h.complementary {2, 3, 5, 9} {0, 1, 4} a269 (by decide) (by decide)
  have he : ( {2, 3, 5, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n117)

end BorsukNine.FiniteObstruction

end OAI
