import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c6355 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a153 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {4, 6} {1, 7, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c6362 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a153 n52 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 8} {4, 7} {1, 6, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c6363 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a153 a52 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {4, 7} {1, 6, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c6409 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a153 a61 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {6, 9} {1, 4, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c6417 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a153 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {7, 9} {1, 4, 6} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c6423 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 5} → T {6, 7, 8} → False := by
  intro a154 a50 a117
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 5} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a50 a117

theorem c6424 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a154 n51 n114
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 6} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n114)

theorem c6426 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 7} → ¬ T {5, 6, 8} → False := by
  intro a154 n52 n112
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n112)

theorem c6427 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 7} → T {5, 6, 8} → False := by
  intro a154 a52 a112
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a112

theorem c6428 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 8} → ¬ T {5, 6, 7} → False := by
  intro a154 n53 n111
  have hc := h.complementary {0, 2, 3, 9} {1, 4, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n53 (hc.mpr n111)

theorem c6430 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 5, 6} → ¬ T {4, 7, 8} → False := by
  intro a154 n55 n108
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 6} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n55 (hc.mpr n108)

theorem c6431 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 6} → T {4, 7, 8} → False := by
  intro a154 a55 a108
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 6} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a55 a108

theorem c6434 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a154 n57 n105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n105)

theorem c6435 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {4, 6, 7} → False := by
  intro a154 a57 a105
  have hc := h.complementary {0, 2, 3, 9} {1, 5, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a105

theorem c6436 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a154 n59 n103
  have hc := h.complementary {0, 2, 3, 9} {1, 6, 7} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n59 (hc.mpr n103)

theorem c6438 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 6, 8} → ¬ T {4, 5, 7} → False := by
  intro a154 n60 n102
  have hc := h.complementary {0, 2, 3, 9} {1, 6, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n60 (hc.mpr n102)

theorem c6439 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 6, 8} → T {4, 5, 7} → False := by
  intro a154 a60 a102
  have hc := h.complementary {0, 2, 3, 9} {1, 6, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a60 a102

theorem c6441 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 7, 8} → T {4, 5, 6} → False := by
  intro a154 a62 a101
  have hc := h.complementary {0, 2, 3, 9} {1, 7, 8} a154 (by decide) (by decide)
  have he : ( {0, 2, 3, 9} : Finset Labels)ᶜ \ {1, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a62 a101

theorem c6443 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 5} → T {1, 4, 6} → T {1, 4, 7} → False := by
  intro a154 a50 a51 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 4} {5, 6, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c6473 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 7} → T {1, 6, 7} → T {1, 7, 8} → False := by
  intro a154 a56 a59 a62
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 7} {5, 6, 8} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 7} = {1, 7, 8} by decide)) a62)

theorem c6475 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 4, 8} → T {1, 5, 8} → T {1, 6, 8} → False := by
  intro a154 a53 a57 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {1, 8} {4, 5, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) a53)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) a60)

theorem c6490 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a154 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {4, 6} {1, 5, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c6498 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 7} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → False := by
  intro a154 n52 n102 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {4, 7} {1, 5, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c6502 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → False := by
  intro a154 n52 n105 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {4, 7} {1, 6, 8} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)

theorem c6531 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a154 a57 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {5, 8} {1, 4, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c6535 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → T {1, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a154 a57 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 9} {5, 8} {1, 6, 7} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c6558 (h : TenSystem T Q) :
    Q {0, 2, 3, 9} → ¬ T {1, 7, 8} → ¬ T {5, 7, 8} → ¬ T {6, 7, 8} → False := by
  intro a154 n62 n114 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 9} {7, 8} {1, 5, 6} a154 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)

theorem c6563 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {1, 3, 6} → T {7, 8, 9} → False := by
  intro a155 a46 a120
  have hc := h.complementary {0, 2, 4, 5} {1, 3, 6} a155 (by decide) (by decide)
  have he : ( {0, 2, 4, 5} : Finset Labels)ᶜ \ {1, 3, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a46 a120

theorem c6625 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {1, 3, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a155 a46 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {3, 6} {1, 7, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

theorem c6654 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a155 n59 n95 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 5} {6, 7} {1, 3, 8} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c6669 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {3, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a155 a96 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {6, 8} {3, 7, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) a96)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c6671 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {1, 6, 9} → T {3, 6, 9} → T {6, 7, 9} → False := by
  intro a155 a61 a97 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {6, 9} {1, 3, 7} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c6685 (h : TenSystem T Q) :
    Q {0, 2, 4, 5} → T {3, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a155 a98 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 5} {7, 8} {3, 6, 9} a155 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) a98)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c6708 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 3, 9} → ¬ T {5, 7, 8} → False := by
  intro a156 n49 n114
  have hc := h.complementary {0, 2, 4, 6} {1, 3, 9} a156 (by decide) (by decide)
  have he : ( {0, 2, 4, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n114)

theorem c6709 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 3, 9} → T {5, 7, 8} → False := by
  intro a156 a49 a114
  have hc := h.complementary {0, 2, 4, 6} {1, 3, 9} a156 (by decide) (by decide)
  have he : ( {0, 2, 4, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a114

theorem c6721 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 8, 9} → T {3, 5, 7} → False := by
  intro a156 a64 a92
  have hc := h.complementary {0, 2, 4, 6} {1, 8, 9} a156 (by decide) (by decide)
  have he : ( {0, 2, 4, 6} : Finset Labels)ᶜ \ {1, 8, 9} = {3, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a64 a92

theorem c6727 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 3, 5} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a156 a45 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 6} {1, 3} {5, 8, 9} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c6757 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 3, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a156 a49 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 6} {1, 9} {3, 5, 8} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c6786 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 3, 9} → ¬ T {3, 5, 9} → ¬ T {3, 7, 9} → False := by
  intro a156 n49 n94 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {3, 9} {1, 5, 7} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c6790 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 3, 9} → ¬ T {3, 7, 9} → ¬ T {3, 8, 9} → False := by
  intro a156 n49 n99 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {3, 9} {1, 7, 8} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c6802 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a156 n57 n93 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {5, 8} {1, 3, 7} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c6818 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → ¬ T {1, 7, 8} → ¬ T {3, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a156 n62 n98 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 6} {7, 8} {1, 3, 5} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)

theorem c6835 (h : TenSystem T Q) :
    Q {0, 2, 4, 6} → T {1, 8, 9} → T {3, 8, 9} → T {5, 8, 9} → False := by
  intro a156 a64 a100 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 6} {8, 9} {1, 3, 5} a156 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c6843 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 5} → T {6, 8, 9} → False := by
  intro a157 a45 a119
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 5} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a45 a119

theorem c6847 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 8} → T {5, 6, 9} → False := by
  intro a157 a48 a113
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 8} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a48 a113

theorem c6848 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 3, 9} → ¬ T {5, 6, 8} → False := by
  intro a157 n49 n112
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 9} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n112)

end BorsukNine.FiniteObstruction

end OAI
