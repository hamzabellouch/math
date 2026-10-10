import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c15953 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 4, 7} → T {3, 5, 8} → False := by
  intro a222 a24 a93
  have hc := h.complementary {1, 2, 6, 9} {0, 4, 7} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a93

theorem c15959 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 5, 8} → T {3, 4, 7} → False := by
  intro a222 a29 a88
  have hc := h.complementary {1, 2, 6, 9} {0, 5, 8} a222 (by decide) (by decide)
  have he : ( {1, 2, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a88

theorem c15986 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {0, 3, 7} → ¬ T {0, 4, 7} → ¬ T {0, 5, 7} → False := by
  intro a222 n19 n24 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 9} {0, 7} {3, 4, 5} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n19 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) ht)

theorem c15988 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {0, 3, 7} → ¬ T {0, 4, 7} → ¬ T {0, 7, 8} → False := by
  intro a222 n19 n24 n34
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 9} {0, 7} {3, 4, 8} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n19 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) ht)
  · exact n24 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) ht)
  · exact n34 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 7} = {0, 7, 8} by decide)) ht)

theorem c16009 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 8} → False := by
  intro a222 a86 a88 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 9} {3, 4} {5, 7, 8} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c16026 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → ¬ T {0, 3, 8} → ¬ T {3, 4, 8} → ¬ T {3, 5, 8} → False := by
  intro a222 n20 n89 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 6, 9} {3, 8} {0, 4, 5} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n20 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 8} = {0, 3, 8} by decide)) ht)
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 8} = {3, 5, 8} by decide)) ht)

theorem c16047 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 8} → False := by
  intro a222 a24 a102 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 9} {4, 7} {0, 5, 8} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c16071 (h : TenSystem T Q) :
    Q {1, 2, 6, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a222 a29 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 6, 9} {5, 8} {0, 4, 7} a222 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c16084 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → ¬ T {0, 3, 5} → ¬ T {4, 6, 9} → False := by
  intro a223 n17 n107
  have hc := h.complementary {1, 2, 7, 8} {0, 3, 5} a223 (by decide) (by decide)
  have he : ( {1, 2, 7, 8} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n107)

theorem c16097 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {0, 5, 6} → T {3, 4, 9} → False := by
  intro a223 a27 a90
  have hc := h.complementary {1, 2, 7, 8} {0, 5, 6} a223 (by decide) (by decide)
  have he : ( {1, 2, 7, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a90

theorem c16149 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a223 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 8} {3, 4} {5, 6, 9} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c16184 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 9} → False := by
  intro a223 n23 n87 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 7, 8} {4, 6} {0, 3, 9} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c16185 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 9} → False := by
  intro a223 a23 a87 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 8} {4, 6} {0, 3, 9} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c16218 (h : TenSystem T Q) :
    Q {1, 2, 7, 8} → ¬ T {0, 6, 9} → ¬ T {4, 6, 9} → ¬ T {5, 6, 9} → False := by
  intro a223 n33 n107 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 7, 8} {6, 9} {0, 4, 5} a223 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n33 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)

theorem c16222 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {0, 3, 4} → ¬ T {5, 6, 8} → False := by
  intro a224 n16 n112
  have hc := h.complementary {1, 2, 7, 9} {0, 3, 4} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n112)

theorem c16225 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 3, 5} → T {4, 6, 8} → False := by
  intro a224 a17 a106
  have hc := h.complementary {1, 2, 7, 9} {0, 3, 5} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a17 a106

theorem c16226 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {0, 3, 6} → ¬ T {4, 5, 8} → False := by
  intro a224 n18 n103
  have hc := h.complementary {1, 2, 7, 9} {0, 3, 6} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n103)

theorem c16229 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 3, 8} → T {4, 5, 6} → False := by
  intro a224 a20 a101
  have hc := h.complementary {1, 2, 7, 9} {0, 3, 8} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a20 a101

theorem c16233 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 6} → T {3, 5, 8} → False := by
  intro a224 a23 a93
  have hc := h.complementary {1, 2, 7, 9} {0, 4, 6} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a93

theorem c16239 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 5, 8} → T {3, 4, 6} → False := by
  intro a224 a29 a87
  have hc := h.complementary {1, 2, 7, 9} {0, 5, 8} a224 (by decide) (by decide)
  have he : ( {1, 2, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a87

theorem c16281 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a224 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {0, 8} {4, 5, 6} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c16289 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a224 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {3, 4} {5, 6, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c16322 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 5, 6} → False := by
  intro a224 n23 n87 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 7, 9} {4, 6} {0, 3, 5} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)

theorem c16324 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 8} → False := by
  intro a224 n23 n87 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 7, 9} {4, 6} {0, 3, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)

theorem c16327 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a224 a23 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {4, 6} {0, 5, 8} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c16349 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a224 a29 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {5, 8} {0, 3, 6} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c16351 (h : TenSystem T Q) :
    Q {1, 2, 7, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a224 a29 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 7, 9} {5, 8} {0, 4, 6} a224 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c16365 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 3, 5} → T {4, 6, 7} → False := by
  intro a225 a17 a105
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 5} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a17 a105

theorem c16368 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 7} → ¬ T {4, 5, 6} → False := by
  intro a225 n19 n101
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n19 (hc.mpr n101)

theorem c16369 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 3, 7} → T {4, 5, 6} → False := by
  intro a225 a19 a101
  have hc := h.complementary {1, 2, 8, 9} {0, 3, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a19 a101

theorem c16374 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 5, 6} → False := by
  intro a225 n24 n91
  have hc := h.complementary {1, 2, 8, 9} {0, 4, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n91)

theorem c16375 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 7} → T {3, 5, 6} → False := by
  intro a225 a24 a91
  have hc := h.complementary {1, 2, 8, 9} {0, 4, 7} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a24 a91

theorem c16376 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 5, 6} → ¬ T {3, 4, 7} → False := by
  intro a225 n27 n88
  have hc := h.complementary {1, 2, 8, 9} {0, 5, 6} a225 (by decide) (by decide)
  have he : ( {1, 2, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n88)

theorem c16384 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 4} → ¬ T {0, 3, 5} → ¬ T {0, 3, 7} → False := by
  intro a225 n16 n17 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {0, 3} {4, 5, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) ht)

theorem c16388 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 3, 5} → ¬ T {0, 3, 6} → ¬ T {0, 3, 7} → False := by
  intro a225 n17 n18 n19
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {0, 3} {5, 6, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) ht)
  · exact n19 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) ht)

theorem c16417 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 3, 7} → T {0, 4, 7} → T {0, 6, 7} → False := by
  intro a225 a19 a24 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {0, 7} {3, 4, 6} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 7} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c16464 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a225 n23 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {4, 6} {0, 3, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c16465 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a225 a23 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {4, 6} {0, 3, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c16467 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a225 a23 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {4, 6} {0, 5, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c16472 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a225 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {4, 7} {0, 3, 6} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c16473 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a225 a24 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {4, 7} {0, 3, 6} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c16483 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {0, 5, 6} → T {4, 5, 6} → T {5, 6, 7} → False := by
  intro a225 a27 a101 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {5, 6} {0, 4, 7} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c16494 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a225 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 8, 9} {6, 7} {0, 3, 4} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c16501 (h : TenSystem T Q) :
    Q {1, 2, 8, 9} → T {3, 6, 7} → T {4, 6, 7} → T {5, 6, 7} → False := by
  intro a225 a95 a105 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 8, 9} {6, 7} {3, 4, 5} a225 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)

theorem c16504 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ T {0, 2, 7} → ¬ T {6, 8, 9} → False := by
  intro a226 n13 n119
  have hc := h.complementary {1, 3, 4, 5} {0, 2, 7} a226 (by decide) (by decide)
  have he : ( {1, 3, 4, 5} : Finset Labels)ᶜ \ {0, 2, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n119)

theorem c16530 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → ¬ T {0, 2, 6} → ¬ T {0, 6, 7} → ¬ T {0, 6, 8} → False := by
  intro a226 n12 n31 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 5} {0, 6} {2, 7, 8} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n31 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
