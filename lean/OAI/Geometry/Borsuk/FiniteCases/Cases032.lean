import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c7251 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 6, 8} → T {5, 6, 8} → T {6, 7, 8} → False := by
  intro a159 a60 a112 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {6, 8} {1, 5, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) a60)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c7266 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {1, 3, 8} → ¬ T {4, 7, 9} → False := by
  intro a160 n48 n109
  have hc := h.complementary {0, 2, 5, 6} {1, 3, 8} a160 (by decide) (by decide)
  have he : ( {0, 2, 5, 6} : Finset Labels)ᶜ \ {1, 3, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n48 (hc.mpr n109)

theorem c7268 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → ¬ T {1, 3, 9} → ¬ T {4, 7, 8} → False := by
  intro a160 n49 n108
  have hc := h.complementary {0, 2, 5, 6} {1, 3, 9} a160 (by decide) (by decide)
  have he : ( {0, 2, 5, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n108)

theorem c7269 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 3, 9} → T {4, 7, 8} → False := by
  intro a160 a49 a108
  have hc := h.complementary {0, 2, 5, 6} {1, 3, 9} a160 (by decide) (by decide)
  have he : ( {0, 2, 5, 6} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a108

theorem c7371 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 4, 9} → T {3, 4, 9} → T {4, 7, 9} → False := by
  intro a160 a54 a90 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 6} {4, 9} {1, 3, 7} a160 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c7395 (h : TenSystem T Q) :
    Q {0, 2, 5, 6} → T {1, 8, 9} → T {3, 8, 9} → T {4, 8, 9} → False := by
  intro a160 a64 a100 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 6} {8, 9} {1, 3, 4} a160 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)

theorem c7411 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 4, 6} → T {3, 8, 9} → False := by
  intro a161 a51 a100
  have hc := h.complementary {0, 2, 5, 7} {1, 4, 6} a161 (by decide) (by decide)
  have he : ( {0, 2, 5, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a100

theorem c7425 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a161 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {1, 3} {4, 6, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7441 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 3, 6} → T {1, 4, 6} → T {1, 6, 9} → False := by
  intro a161 a46 a51 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {1, 6} {3, 4, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 6} = {1, 6, 9} by decide)) a61)

theorem c7469 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {3, 4, 6} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a161 a87 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {3, 4} {6, 8, 9} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c7513 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → T {1, 4, 9} → T {3, 4, 9} → T {4, 8, 9} → False := by
  intro a161 a54 a90 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 7} {4, 9} {1, 3, 8} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c7534 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a161 n64 n100 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 7} {8, 9} {1, 3, 4} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c7536 (h : TenSystem T Q) :
    Q {0, 2, 5, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a161 n64 n100 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 7} {8, 9} {1, 3, 6} a161 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c7548 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 3, 9} → ¬ T {4, 6, 7} → False := by
  intro a162 n49 n105
  have hc := h.complementary {0, 2, 5, 8} {1, 3, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n105)

theorem c7549 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 9} → T {4, 6, 7} → False := by
  intro a162 a49 a105
  have hc := h.complementary {0, 2, 5, 8} {1, 3, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a105

theorem c7555 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 9} → T {3, 6, 7} → False := by
  intro a162 a54 a95
  have hc := h.complementary {0, 2, 5, 8} {1, 4, 9} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 4, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a54 a95

theorem c7557 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 6, 7} → T {3, 4, 9} → False := by
  intro a162 a59 a90
  have hc := h.complementary {0, 2, 5, 8} {1, 6, 7} a162 (by decide) (by decide)
  have he : ( {0, 2, 5, 8} : Finset Labels)ᶜ \ {1, 6, 7} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a90

theorem c7565 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a162 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 3} {4, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7573 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a162 a44 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 4} {3, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c7578 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a162 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {1, 6} {3, 4, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c7592 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 4, 7} → ¬ T {1, 6, 7} → ¬ T {1, 7, 9} → False := by
  intro a162 n52 n59 n63
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {1, 7} {4, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) ht)
  · exact n63 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) ht)

theorem c7597 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 9} → T {1, 4, 9} → T {1, 7, 9} → False := by
  intro a162 a49 a54 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {1, 9} {3, 4, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c7615 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a162 a46 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 6} {1, 7, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

theorem c7621 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 3, 7} → T {3, 4, 7} → T {3, 7, 9} → False := by
  intro a162 a47 a88 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 7} {1, 4, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c7625 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {3, 4, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a162 a88 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {3, 7} {4, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c7634 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a162 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {4, 6} {1, 3, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c7635 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a162 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 6} {1, 3, 7} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c7639 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a162 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 6} {1, 7, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c7640 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a162 n87 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 8} {4, 6} {3, 7, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c7647 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {1, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a162 a52 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 7} {1, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c7649 (h : TenSystem T Q) :
    Q {0, 2, 5, 8} → T {3, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a162 a88 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 8} {4, 7} {3, 6, 9} a162 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c7683 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 3, 4} → T {6, 7, 8} → False := by
  intro a163 a44 a117
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 4} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a44 a117

theorem c7685 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 3, 6} → T {4, 7, 8} → False := by
  intro a163 a46 a108
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 6} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a108

theorem c7688 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {1, 3, 8} → ¬ T {4, 6, 7} → False := by
  intro a163 n48 n105
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 8} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n48 (hc.mpr n105)

theorem c7689 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 3, 8} → T {4, 6, 7} → False := by
  intro a163 a48 a105
  have hc := h.complementary {0, 2, 5, 9} {1, 3, 8} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a48 a105

theorem c7695 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 8} → T {3, 6, 7} → False := by
  intro a163 a53 a95
  have hc := h.complementary {0, 2, 5, 9} {1, 4, 8} a163 (by decide) (by decide)
  have he : ( {0, 2, 5, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a53 a95

theorem c7718 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → ¬ T {1, 6, 7} → False := by
  intro a163 n46 n51 n59
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 9} {1, 6} {3, 4, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) ht)

theorem c7774 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a163 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 5, 9} {4, 6} {1, 3, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c7775 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a163 a51 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {4, 6} {1, 3, 7} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c7783 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {1, 4, 7} → T {3, 4, 7} → T {4, 6, 7} → False := by
  intro a163 a52 a88 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {4, 7} {1, 3, 6} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c7805 (h : TenSystem T Q) :
    Q {0, 2, 5, 9} → T {3, 6, 7} → T {4, 6, 7} → T {6, 7, 8} → False := by
  intro a163 a95 a105 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 5, 9} {6, 7} {3, 4, 8} a163 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c7823 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 3, 4} → T {5, 8, 9} → False := by
  intro a164 a44 a116
  have hc := h.complementary {0, 2, 6, 7} {1, 3, 4} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 3, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a44 a116

theorem c7828 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 3, 9} → ¬ T {4, 5, 8} → False := by
  intro a164 n49 n103
  have hc := h.complementary {0, 2, 6, 7} {1, 3, 9} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n103)

theorem c7829 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 3, 9} → T {4, 5, 8} → False := by
  intro a164 a49 a103
  have hc := h.complementary {0, 2, 6, 7} {1, 3, 9} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a103

theorem c7837 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 5, 8} → T {3, 4, 9} → False := by
  intro a164 a57 a90
  have hc := h.complementary {0, 2, 6, 7} {1, 5, 8} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a90

theorem c7841 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 8, 9} → T {3, 4, 5} → False := by
  intro a164 a64 a86
  have hc := h.complementary {0, 2, 6, 7} {1, 8, 9} a164 (by decide) (by decide)
  have he : ( {0, 2, 6, 7} : Finset Labels)ᶜ \ {1, 8, 9} = {3, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a64 a86

end BorsukNine.FiniteObstruction

end OAI
