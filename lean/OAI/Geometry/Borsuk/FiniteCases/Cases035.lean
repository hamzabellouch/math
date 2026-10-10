import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c9181 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a173 a76 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {5, 6} {2, 7, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c9189 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a173 a77 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {5, 7} {2, 6, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c9203 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a173 a59 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {6, 7} {1, 5, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9205 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a173 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {6, 7} {2, 5, 9} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9215 (h : TenSystem T Q) :
    Q {0, 3, 4, 8} → T {1, 7, 9} → T {2, 7, 9} → T {5, 7, 9} → False := by
  intro a173 a63 a84 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 8} {7, 9} {1, 2, 5} a173 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)

theorem c9222 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 5} → ¬ T {6, 7, 8} → False := by
  intro a174 n39 n117
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 5} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n117)

theorem c9223 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 2, 5} → T {6, 7, 8} → False := by
  intro a174 a39 a117
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 5} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a39 a117

theorem c9224 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 6} → ¬ T {5, 7, 8} → False := by
  intro a174 n40 n114
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 6} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n114)

theorem c9226 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n41 n112
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 7} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n112)

theorem c9228 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 2, 8} → ¬ T {5, 6, 7} → False := by
  intro a174 n42 n111
  have hc := h.complementary {0, 3, 4, 9} {1, 2, 8} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n111)

theorem c9235 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 5, 8} → T {2, 6, 7} → False := by
  intro a174 a57 a80
  have hc := h.complementary {0, 3, 4, 9} {1, 5, 8} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a80

theorem c9237 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 6, 7} → T {2, 5, 8} → False := by
  intro a174 a59 a78
  have hc := h.complementary {0, 3, 4, 9} {1, 6, 7} a174 (by decide) (by decide)
  have he : ( {0, 3, 4, 9} : Finset Labels)ᶜ \ {1, 6, 7} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a59 a78

theorem c9273 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a174 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {1, 7} {5, 6, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

theorem c9291 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a174 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {2, 6} {1, 5, 7} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c9318 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n55 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 6} {1, 7, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n55 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c9320 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a174 n76 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 6} {2, 7, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c9330 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a174 n57 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {5, 8} {1, 2, 6} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c9333 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {1, 5, 8} → T {2, 5, 8} → T {5, 7, 8} → False := by
  intro a174 a57 a78 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {5, 8} {1, 2, 7} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c9342 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → ¬ T {1, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a174 n59 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 4, 9} {6, 7} {1, 5, 8} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c9361 (h : TenSystem T Q) :
    Q {0, 3, 4, 9} → T {2, 7, 8} → T {5, 7, 8} → T {6, 7, 8} → False := by
  intro a174 a83 a114 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 4, 9} {7, 8} {2, 5, 6} a174 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) a83)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)

theorem c9362 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 4} → ¬ T {7, 8, 9} → False := by
  intro a175 n38 n120
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 4} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n120)

theorem c9363 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 2, 4} → T {7, 8, 9} → False := by
  intro a175 a38 a120
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 4} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 4} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a120

theorem c9364 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 7} → ¬ T {4, 8, 9} → False := by
  intro a175 n41 n110
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 7} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n110)

theorem c9365 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 2, 7} → T {4, 8, 9} → False := by
  intro a175 a41 a110
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 7} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a110

theorem c9366 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → ¬ T {1, 2, 8} → ¬ T {4, 7, 9} → False := by
  intro a175 n42 n109
  have hc := h.complementary {0, 3, 5, 6} {1, 2, 8} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n109)

theorem c9373 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 4, 8} → T {2, 7, 9} → False := by
  intro a175 a53 a84
  have hc := h.complementary {0, 3, 5, 6} {1, 4, 8} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 4, 8} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a53 a84

theorem c9379 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {1, 7, 9} → T {2, 4, 8} → False := by
  intro a175 a63 a74
  have hc := h.complementary {0, 3, 5, 6} {1, 7, 9} a175 (by decide) (by decide)
  have he : ( {0, 3, 5, 6} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a63 a74

theorem c9477 (h : TenSystem T Q) :
    Q {0, 3, 5, 6} → T {2, 4, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a175 a75 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 6} {4, 9} {2, 7, 8} a175 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c9503 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 2, 4} → T {6, 8, 9} → False := by
  intro a176 a38 a119
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 4} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a119

theorem c9506 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {1, 2, 8} → ¬ T {4, 6, 9} → False := by
  intro a176 n42 n107
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 8} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n107)

theorem c9508 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {1, 2, 9} → ¬ T {4, 6, 8} → False := by
  intro a176 n43 n106
  have hc := h.complementary {0, 3, 5, 7} {1, 2, 9} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n106)

theorem c9517 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 6, 8} → T {2, 4, 9} → False := by
  intro a176 a60 a75
  have hc := h.complementary {0, 3, 5, 7} {1, 6, 8} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 6, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a75

theorem c9521 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 8, 9} → T {2, 4, 6} → False := by
  intro a176 a64 a72
  have hc := h.complementary {0, 3, 5, 7} {1, 8, 9} a176 (by decide) (by decide)
  have he : ( {0, 3, 5, 7} : Finset Labels)ᶜ \ {1, 8, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a64 a72

theorem c9524 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → ¬ T {1, 2, 4} → ¬ T {1, 2, 6} → ¬ T {1, 2, 9} → False := by
  intro a176 n38 n40 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 7} {1, 2} {4, 6, 9} a176 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

theorem c9573 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 2, 6} → T {2, 4, 6} → T {2, 6, 9} → False := by
  intro a176 a40 a72 a82
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 7} {2, 6} {1, 4, 9} a176 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) a82)

theorem c9615 (h : TenSystem T Q) :
    Q {0, 3, 5, 7} → T {1, 4, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a176 a54 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 7} {4, 9} {1, 6, 8} a176 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c9642 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 4} → ¬ T {6, 7, 9} → False := by
  intro a177 n38 n118
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 4} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n118)

theorem c9644 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → ¬ T {4, 7, 9} → False := by
  intro a177 n40 n109
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n109)

theorem c9645 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 6} → T {4, 7, 9} → False := by
  intro a177 a40 a109
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a109

theorem c9646 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 7} → ¬ T {4, 6, 9} → False := by
  intro a177 n41 n107
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 7} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n107)

theorem c9647 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 7} → T {4, 6, 9} → False := by
  intro a177 a41 a107
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 7} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a107

theorem c9648 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 9} → ¬ T {4, 6, 7} → False := by
  intro a177 n43 n105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n105)

theorem c9649 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 9} → T {4, 6, 7} → False := by
  intro a177 a43 a105
  have hc := h.complementary {0, 3, 5, 8} {1, 2, 9} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a43 a105

theorem c9651 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 6} → T {2, 7, 9} → False := by
  intro a177 a51 a84
  have hc := h.complementary {0, 3, 5, 8} {1, 4, 6} a177 (by decide) (by decide)
  have he : ( {0, 3, 5, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a84

theorem c9665 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 2, 4} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a177 a38 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {1, 2} {4, 6, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c9710 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a177 n40 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {2, 6} {1, 4, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c9730 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 2, 9} → ¬ T {2, 6, 9} → ¬ T {2, 7, 9} → False := by
  intro a177 n43 n82 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {2, 9} {1, 6, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) ht)

theorem c9735 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a177 a51 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 6} {1, 2, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

end BorsukNine.FiniteObstruction

end OAI
