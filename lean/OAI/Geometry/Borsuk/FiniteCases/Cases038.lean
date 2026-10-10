import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c10870 (h : TenSystem T Q) :
    Q {0, 4, 5, 6} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 7, 9} → False := by
  intro a185 n49 n70 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 6} {3, 9} {1, 2, 7} a185 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c10903 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {6, 8, 9} → False := by
  intro a186 a37 a119
  have hc := h.complementary {0, 4, 5, 7} {1, 2, 3} a186 (by decide) (by decide)
  have he : ( {0, 4, 5, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a119

theorem c10925 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a186 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {1, 2} {3, 6, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c10933 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a186 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {1, 3} {2, 6, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c10935 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a186 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {1, 3} {2, 8, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c10965 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a186 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {2, 3} {1, 6, 9} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11012 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 8, 9} → False := by
  intro a186 n49 n70 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 7} {3, 9} {1, 2, 8} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c11013 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → T {1, 3, 9} → T {2, 3, 9} → T {3, 8, 9} → False := by
  intro a186 a49 a70 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 7} {3, 9} {1, 2, 8} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c11032 (h : TenSystem T Q) :
    Q {0, 4, 5, 7} → ¬ T {2, 6, 9} → ¬ T {3, 6, 9} → ¬ T {6, 8, 9} → False := by
  intro a186 n82 n97 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 7} {6, 9} {2, 3, 8} a186 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

theorem c11043 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {6, 7, 9} → False := by
  intro a187 a37 a118
  have hc := h.complementary {0, 4, 5, 8} {1, 2, 3} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a118

theorem c11048 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 2, 9} → ¬ T {3, 6, 7} → False := by
  intro a187 n43 n95
  have hc := h.complementary {0, 4, 5, 8} {1, 2, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n95)

theorem c11052 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 7} → ¬ T {2, 6, 9} → False := by
  intro a187 n47 n82
  have hc := h.complementary {0, 4, 5, 8} {1, 3, 7} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 6, 9} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n82)

theorem c11054 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 9} → ¬ T {2, 6, 7} → False := by
  intro a187 n49 n80
  have hc := h.complementary {0, 4, 5, 8} {1, 3, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n80)

theorem c11058 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 6, 9} → ¬ T {2, 3, 7} → False := by
  intro a187 n61 n68
  have hc := h.complementary {0, 4, 5, 8} {1, 6, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 6, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n61 (hc.mpr n68)

theorem c11061 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 7, 9} → T {2, 3, 6} → False := by
  intro a187 a63 a67
  have hc := h.complementary {0, 4, 5, 8} {1, 7, 9} a187 (by decide) (by decide)
  have he : ( {0, 4, 5, 8} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a63 a67

theorem c11065 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a187 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 2} {3, 6, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11067 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a187 a37 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 2} {3, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11068 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 2, 6} → ¬ T {1, 2, 7} → ¬ T {1, 2, 9} → False := by
  intro a187 n40 n41 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {1, 2} {6, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

theorem c11073 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a187 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 3} {2, 6, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11075 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a187 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 3} {2, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11076 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 6} → ¬ T {1, 3, 7} → ¬ T {1, 3, 9} → False := by
  intro a187 n46 n47 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {1, 3} {6, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c11087 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 7} → T {1, 3, 7} → T {1, 6, 7} → False := by
  intro a187 a41 a47 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 7} {2, 3, 6} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)

theorem c11097 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 7, 9} → False := by
  intro a187 a43 a49 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {1, 9} {2, 3, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c11115 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 6} → T {2, 6, 7} → T {2, 6, 9} → False := by
  intro a187 a40 a80 a82
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {2, 6} {1, 7, 9} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) a82)

theorem c11119 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 2, 7} → T {2, 3, 7} → T {2, 6, 7} → False := by
  intro a187 a41 a68 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {2, 7} {1, 3, 6} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c11133 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {2, 3, 9} → T {2, 6, 9} → T {2, 7, 9} → False := by
  intro a187 a70 a82 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {2, 9} {3, 6, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c11134 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 7} → False := by
  intro a187 n46 n67 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {3, 6} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c11150 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 6, 9} → False := by
  intro a187 n49 n70 n97
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {3, 9} {1, 2, 6} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) ht)

theorem c11152 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 7, 9} → False := by
  intro a187 n49 n70 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {3, 9} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c11153 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a187 a49 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 8} {3, 9} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c11168 (h : TenSystem T Q) :
    Q {0, 4, 5, 8} → ¬ T {1, 6, 9} → ¬ T {2, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a187 n61 n82 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 5, 8} {6, 9} {1, 2, 7} a187 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n61 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c11183 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → T {1, 2, 3} → T {6, 7, 8} → False := by
  intro a188 a37 a117
  have hc := h.complementary {0, 4, 5, 9} {1, 2, 3} a188 (by decide) (by decide)
  have he : ( {0, 4, 5, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a117

theorem c11211 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a188 a37 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 9} {1, 3} {2, 6, 7} a188 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c11315 (h : TenSystem T Q) :
    Q {0, 4, 5, 9} → T {1, 7, 8} → T {2, 7, 8} → T {3, 7, 8} → False := by
  intro a188 a62 a83 a98
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 5, 9} {7, 8} {1, 2, 3} a188 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) a62)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) a83)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) a98)

theorem c11323 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {5, 8, 9} → False := by
  intro a189 a37 a116
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 3} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a116

theorem c11325 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 5} → T {3, 8, 9} → False := by
  intro a189 a39 a100
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 5} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 5} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a39 a100

theorem c11326 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 2, 8} → ¬ T {3, 5, 9} → False := by
  intro a189 n42 n94
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 8} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 8} = {3, 5, 9} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n94)

theorem c11328 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 2, 9} → ¬ T {3, 5, 8} → False := by
  intro a189 n43 n93
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n93)

theorem c11329 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 9} → T {3, 5, 8} → False := by
  intro a189 a43 a93
  have hc := h.complementary {0, 4, 6, 7} {1, 2, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a43 a93

theorem c11330 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 5} → ¬ T {2, 8, 9} → False := by
  intro a189 n45 n85
  have hc := h.complementary {0, 4, 6, 7} {1, 3, 5} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 8, 9} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n85)

theorem c11334 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 5, 8} → False := by
  intro a189 n49 n78
  have hc := h.complementary {0, 4, 6, 7} {1, 3, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n78)

theorem c11336 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {2, 3, 9} → False := by
  intro a189 n57 n70
  have hc := h.complementary {0, 4, 6, 7} {1, 5, 8} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n70)

theorem c11337 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 5, 8} → T {2, 3, 9} → False := by
  intro a189 a57 a70
  have hc := h.complementary {0, 4, 6, 7} {1, 5, 8} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a70

theorem c11339 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 5, 9} → T {2, 3, 8} → False := by
  intro a189 a58 a69
  have hc := h.complementary {0, 4, 6, 7} {1, 5, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 5, 9} = {2, 3, 8} := by decide
  rw [he] at hc
  exact hc.mp a58 a69

theorem c11341 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 8, 9} → T {2, 3, 5} → False := by
  intro a189 a64 a66
  have hc := h.complementary {0, 4, 6, 7} {1, 8, 9} a189 (by decide) (by decide)
  have he : ( {0, 4, 6, 7} : Finset Labels)ᶜ \ {1, 8, 9} = {2, 3, 5} := by decide
  rw [he] at hc
  exact hc.mp a64 a66

theorem c11345 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a189 a37 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 2} {3, 5, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

end BorsukNine.FiniteObstruction

end OAI
