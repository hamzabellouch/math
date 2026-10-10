import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c2153 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a123 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {4, 7} {3, 6, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c2176 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a123 n95 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 5} {6, 7} {3, 4, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c2207 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a123 a99 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {7, 9} {3, 4, 6} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c2221 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {4, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a123 a110 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {8, 9} {4, 6, 7} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c2224 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {3, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a124 n88 n116
  have hc := h.complementary {0, 1, 2, 6} {3, 4, 7} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n88 (hc.mpr n116)

theorem c2232 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {3, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a124 n93 n109
  have hc := h.complementary {0, 1, 2, 6} {3, 5, 8} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n109)

theorem c2233 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 5, 8} → T {4, 7, 9} → False := by
  intro a124 a93 a109
  have hc := h.complementary {0, 1, 2, 6} {3, 5, 8} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a109

theorem c2235 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 5, 9} → T {4, 7, 8} → False := by
  intro a124 a94 a108
  have hc := h.complementary {0, 1, 2, 6} {3, 5, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 5, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a94 a108

theorem c2239 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 7, 9} → T {4, 5, 8} → False := by
  intro a124 a99 a103
  have hc := h.complementary {0, 1, 2, 6} {3, 7, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a99 a103

theorem c2241 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 8, 9} → T {4, 5, 7} → False := by
  intro a124 a100 a102
  have hc := h.complementary {0, 1, 2, 6} {3, 8, 9} a124 (by decide) (by decide)
  have he : ( {0, 1, 2, 6} : Finset Labels)ᶜ \ {3, 8, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a100 a102

theorem c2247 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 4, 5} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a124 a86 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 6} {3, 4} {5, 8, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2255 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → T {3, 4, 5} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a124 a86 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 6} {3, 5} {4, 8, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2270 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {3, 4, 8} → ¬ T {3, 7, 8} → ¬ T {3, 8, 9} → False := by
  intro a124 n89 n98 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 6} {3, 8} {4, 7, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n89 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 8} = {3, 4, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 8} = {3, 7, 8} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 8} = {3, 8, 9} by decide)) ht)

theorem c2324 (h : TenSystem T Q) :
    Q {0, 1, 2, 6} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a124 n93 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 6} {5, 8} {3, 4, 9} a124 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c2363 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 5} → T {6, 8, 9} → False := by
  intro a125 a86 a119
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 5} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a86 a119

theorem c2365 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 6} → T {5, 8, 9} → False := by
  intro a125 a87 a116
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 6} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a87 a116

theorem c2367 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 8} → T {5, 6, 9} → False := by
  intro a125 a89 a113
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a89 a113

theorem c2368 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {3, 4, 9} → ¬ T {5, 6, 8} → False := by
  intro a125 n90 n112
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 9} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n90 (hc.mpr n112)

theorem c2369 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 9} → T {5, 6, 8} → False := by
  intro a125 a90 a112
  have hc := h.complementary {0, 1, 2, 7} {3, 4, 9} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 4, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a90 a112

theorem c2371 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 6} → T {4, 8, 9} → False := by
  intro a125 a91 a110
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 6} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a91 a110

theorem c2372 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {3, 5, 8} → ¬ T {4, 6, 9} → False := by
  intro a125 n93 n107
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n107)

theorem c2373 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 8} → T {4, 6, 9} → False := by
  intro a125 a93 a107
  have hc := h.complementary {0, 1, 2, 7} {3, 5, 8} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a107

theorem c2378 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → ¬ T {3, 6, 9} → ¬ T {4, 5, 8} → False := by
  intro a125 n97 n103
  have hc := h.complementary {0, 1, 2, 7} {3, 6, 9} a125 (by decide) (by decide)
  have he : ( {0, 1, 2, 7} : Finset Labels)ᶜ \ {3, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n97 (hc.mpr n103)

theorem c2441 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 8} → T {4, 5, 8} → T {4, 8, 9} → False := by
  intro a125 a89 a103 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {4, 8} {3, 5, 9} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 8} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c2449 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a125 a90 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {4, 9} {3, 5, 8} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c2463 (h : TenSystem T Q) :
    Q {0, 1, 2, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a125 a93 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 7} {5, 8} {3, 4, 6} a125 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c2505 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 6} → T {5, 7, 9} → False := by
  intro a126 a87 a115
  have hc := h.complementary {0, 1, 2, 8} {3, 4, 6} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a87 a115

theorem c2506 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → ¬ T {3, 4, 7} → ¬ T {5, 6, 9} → False := by
  intro a126 n88 n113
  have hc := h.complementary {0, 1, 2, 8} {3, 4, 7} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 4, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n88 (hc.mpr n113)

theorem c2509 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 9} → T {5, 6, 7} → False := by
  intro a126 a90 a111
  have hc := h.complementary {0, 1, 2, 8} {3, 4, 9} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 4, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a90 a111

theorem c2515 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 5, 9} → T {4, 6, 7} → False := by
  intro a126 a94 a105
  have hc := h.complementary {0, 1, 2, 8} {3, 5, 9} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a94 a105

theorem c2517 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 6, 7} → T {4, 5, 9} → False := by
  intro a126 a95 a104
  have hc := h.complementary {0, 1, 2, 8} {3, 6, 7} a126 (by decide) (by decide)
  have he : ( {0, 1, 2, 8} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a95 a104

theorem c2525 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a126 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 4} {5, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2533 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {3, 5, 6} → T {3, 5, 9} → False := by
  intro a126 a86 a91 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 5} {4, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c2543 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a126 a87 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 6} {4, 7, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

theorem c2555 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 9} → T {3, 5, 9} → T {3, 6, 9} → False := by
  intro a126 a90 a94 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {3, 9} {4, 5, 6} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c2563 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a126 a86 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {4, 5} {3, 6, 7} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c2583 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a126 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {4, 7} {3, 6, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c2620 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a126 n95 n105 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 8} {6, 7} {3, 4, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c2623 (h : TenSystem T Q) :
    Q {0, 1, 2, 8} → T {3, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a126 a95 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 8} {6, 7} {3, 5, 9} a126 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c2643 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 5} → T {6, 7, 8} → False := by
  intro a127 a86 a117
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 5} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a86 a117

theorem c2644 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a127 n87 n114
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 6} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n87 (hc.mpr n114)

theorem c2645 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 6} → T {5, 7, 8} → False := by
  intro a127 a87 a114
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 6} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a87 a114

theorem c2646 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 4, 7} → ¬ T {5, 6, 8} → False := by
  intro a127 n88 n112
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n88 (hc.mpr n112)

theorem c2647 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 4, 7} → T {5, 6, 8} → False := by
  intro a127 a88 a112
  have hc := h.complementary {0, 1, 2, 9} {3, 4, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a88 a112

theorem c2653 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 7} → T {4, 6, 8} → False := by
  intro a127 a92 a106
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 7} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a92 a106

theorem c2654 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a127 n93 n105
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n105)

theorem c2655 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → T {3, 5, 8} → T {4, 6, 7} → False := by
  intro a127 a93 a105
  have hc := h.complementary {0, 1, 2, 9} {3, 5, 8} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a93 a105

theorem c2656 (h : TenSystem T Q) :
    Q {0, 1, 2, 9} → ¬ T {3, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a127 n95 n103
  have hc := h.complementary {0, 1, 2, 9} {3, 6, 7} a127 (by decide) (by decide)
  have he : ( {0, 1, 2, 9} : Finset Labels)ᶜ \ {3, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n95 (hc.mpr n103)

end BorsukNine.FiniteObstruction

end OAI
