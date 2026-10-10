import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c4147 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a137 a77 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {5, 7} {2, 6, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c4163 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → T {2, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a137 a80 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 8} {6, 7} {2, 5, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c4164 (h : TenSystem T Q) :
    Q {0, 1, 4, 8} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a137 n95 n111 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 4, 8} {6, 7} {3, 5, 9} a137 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c4191 (h : TenSystem T Q) :
    Q {0, 1, 4, 9} → T {2, 5, 6} → T {3, 7, 8} → False := by
  intro a138 a76 a98
  have hc := h.complementary {0, 1, 4, 9} {2, 5, 6} a138 (by decide) (by decide)
  have he : ( {0, 1, 4, 9} : Finset Labels)ᶜ \ {2, 5, 6} = {3, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a76 a98

theorem c4195 (h : TenSystem T Q) :
    Q {0, 1, 4, 9} → T {2, 5, 8} → T {3, 6, 7} → False := by
  intro a138 a78 a95
  have hc := h.complementary {0, 1, 4, 9} {2, 5, 8} a138 (by decide) (by decide)
  have he : ( {0, 1, 4, 9} : Finset Labels)ᶜ \ {2, 5, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a78 a95

theorem c4213 (h : TenSystem T Q) :
    Q {0, 1, 4, 9} → T {2, 3, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a138 a66 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 4, 9} {2, 5} {3, 6, 8} a138 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 5} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c4326 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {2, 3, 8} → ¬ T {4, 7, 9} → False := by
  intro a139 n69 n109
  have hc := h.complementary {0, 1, 5, 6} {2, 3, 8} a139 (by decide) (by decide)
  have he : ( {0, 1, 5, 6} : Finset Labels)ᶜ \ {2, 3, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n69 (hc.mpr n109)

theorem c4328 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → ¬ T {2, 3, 9} → ¬ T {4, 7, 8} → False := by
  intro a139 n70 n108
  have hc := h.complementary {0, 1, 5, 6} {2, 3, 9} a139 (by decide) (by decide)
  have he : ( {0, 1, 5, 6} : Finset Labels)ᶜ \ {2, 3, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n70 (hc.mpr n108)

theorem c4333 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → T {2, 4, 8} → T {3, 7, 9} → False := by
  intro a139 a74 a99
  have hc := h.complementary {0, 1, 5, 6} {2, 4, 8} a139 (by decide) (by decide)
  have he : ( {0, 1, 5, 6} : Finset Labels)ᶜ \ {2, 4, 8} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a74 a99

theorem c4389 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → T {3, 4, 7} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a139 a88 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 6} {3, 4} {7, 8, 9} a139 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c4455 (h : TenSystem T Q) :
    Q {0, 1, 5, 6} → T {2, 8, 9} → T {3, 8, 9} → T {4, 8, 9} → False := by
  intro a139 a85 a100 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 6} {8, 9} {2, 3, 4} a139 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) a85)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)

theorem c4468 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {2, 3, 9} → ¬ T {4, 6, 8} → False := by
  intro a140 n70 n106
  have hc := h.complementary {0, 1, 5, 7} {2, 3, 9} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 3, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n70 (hc.mpr n106)

theorem c4471 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 4, 6} → T {3, 8, 9} → False := by
  intro a140 a72 a100
  have hc := h.complementary {0, 1, 5, 7} {2, 4, 6} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a100

theorem c4479 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 6, 9} → T {3, 4, 8} → False := by
  intro a140 a82 a89
  have hc := h.complementary {0, 1, 5, 7} {2, 6, 9} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 6, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a82 a89

theorem c4481 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 8, 9} → T {3, 4, 6} → False := by
  intro a140 a85 a87
  have hc := h.complementary {0, 1, 5, 7} {2, 8, 9} a140 (by decide) (by decide)
  have he : ( {0, 1, 5, 7} : Finset Labels)ᶜ \ {2, 8, 9} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a85 a87

theorem c4521 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → T {2, 4, 9} → T {2, 6, 9} → T {2, 8, 9} → False := by
  intro a140 a75 a82 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 7} {2, 9} {4, 6, 8} a140 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c4584 (h : TenSystem T Q) :
    Q {0, 1, 5, 7} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a140 n96 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 7} {6, 8} {3, 4, 9} a140 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c4604 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 3, 6} → ¬ T {4, 7, 9} → False := by
  intro a141 n67 n109
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n67 (hc.mpr n109)

theorem c4605 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 6} → T {4, 7, 9} → False := by
  intro a141 a67 a109
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a67 a109

theorem c4607 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 7} → T {4, 6, 9} → False := by
  intro a141 a68 a107
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 7} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a68 a107

theorem c4609 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 9} → T {4, 6, 7} → False := by
  intro a141 a70 a105
  have hc := h.complementary {0, 1, 5, 8} {2, 3, 9} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a70 a105

theorem c4611 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 6} → T {3, 7, 9} → False := by
  intro a141 a72 a99
  have hc := h.complementary {0, 1, 5, 8} {2, 4, 6} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a99

theorem c4621 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 7, 9} → T {3, 4, 6} → False := by
  intro a141 a84 a87
  have hc := h.complementary {0, 1, 5, 8} {2, 7, 9} a141 (by decide) (by decide)
  have he : ( {0, 1, 5, 8} : Finset Labels)ᶜ \ {2, 7, 9} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a84 a87

theorem c4638 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 3, 6} → ¬ T {2, 4, 6} → ¬ T {2, 6, 7} → False := by
  intro a141 n67 n72 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {2, 6} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c4657 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a141 a70 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {2, 9} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c4682 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 3, 7} → ¬ T {3, 6, 7} → ¬ T {3, 7, 9} → False := by
  intro a141 n68 n95 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {3, 7} {2, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n68 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 7} = {2, 3, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) ht)

theorem c4685 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a141 a88 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {3, 7} {4, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c4689 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a141 a70 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {3, 9} {2, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c4694 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a141 n72 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {4, 6} {2, 3, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c4695 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a141 a72 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 6} {2, 3, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c4699 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a141 a72 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 6} {2, 7, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c4700 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a141 n87 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {4, 6} {3, 7, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c4707 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a141 a73 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 7} {2, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c4708 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a141 n88 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {4, 7} {3, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c4709 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a141 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 7} {3, 6, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c4717 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a141 a90 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {4, 9} {3, 6, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c4719 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {2, 6, 7} → T {3, 6, 7} → T {4, 6, 7} → False := by
  intro a141 a80 a95 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {6, 7} {2, 3, 4} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)

theorem c4725 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a141 a95 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {6, 7} {3, 4, 9} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c4730 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a141 n82 n107 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {6, 9} {2, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c4733 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → T {3, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a141 a97 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 8} {6, 9} {3, 4, 7} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c4736 (h : TenSystem T Q) :
    Q {0, 1, 5, 8} → ¬ T {2, 7, 9} → ¬ T {3, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a141 n84 n99 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 5, 8} {7, 9} {2, 3, 6} a141 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n84 (Eq.mp (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)

theorem c4751 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → T {2, 4, 6} → T {3, 7, 8} → False := by
  intro a142 a72 a98
  have hc := h.complementary {0, 1, 5, 9} {2, 4, 6} a142 (by decide) (by decide)
  have he : ( {0, 1, 5, 9} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a72 a98

theorem c4865 (h : TenSystem T Q) :
    Q {0, 1, 5, 9} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 8} → False := by
  intro a142 a95 a105 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 5, 9} {6, 7} {3, 4, 8} a142 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c4882 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ T {2, 3, 4} → ¬ T {5, 8, 9} → False := by
  intro a143 n65 n116
  have hc := h.complementary {0, 1, 6, 7} {2, 3, 4} a143 (by decide) (by decide)
  have he : ( {0, 1, 6, 7} : Finset Labels)ᶜ \ {2, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n65 (hc.mpr n116)

theorem c4891 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 4, 5} → T {3, 8, 9} → False := by
  intro a143 a71 a100
  have hc := h.complementary {0, 1, 6, 7} {2, 4, 5} a143 (by decide) (by decide)
  have he : ( {0, 1, 6, 7} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a100

theorem c4895 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 4, 9} → T {3, 5, 8} → False := by
  intro a143 a75 a93
  have hc := h.complementary {0, 1, 6, 7} {2, 4, 9} a143 (by decide) (by decide)
  have he : ( {0, 1, 6, 7} : Finset Labels)ᶜ \ {2, 4, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a75 a93

end BorsukNine.FiniteObstruction

end OAI
