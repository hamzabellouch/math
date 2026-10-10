import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c11347 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 2, 8} → T {1, 2, 9} → False := by
  intro a189 a37 a42 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 2} {3, 8, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11353 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a189 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 3} {2, 5, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11355 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a189 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 3} {2, 8, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11374 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 5, 9} → False := by
  intro a189 n43 n49 n58
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {1, 9} {2, 3, 5} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) ht)

theorem c11376 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 8, 9} → False := by
  intro a189 n43 n49 n64
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {1, 9} {2, 3, 8} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) ht)

theorem c11379 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a189 a43 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {1, 9} {2, 5, 8} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c11385 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {2, 3, 5} → T {2, 3, 9} → False := by
  intro a189 a37 a66 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {2, 3} {1, 5, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11387 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a189 a37 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {2, 3} {1, 8, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11414 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 5} → ¬ T {2, 3, 5} → ¬ T {3, 5, 8} → False := by
  intro a189 n45 n66 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {3, 5} {1, 2, 8} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 5} = {2, 3, 5} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c11430 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 5, 9} → False := by
  intro a189 n49 n70 n94
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {3, 9} {1, 2, 5} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)

theorem c11432 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 8, 9} → False := by
  intro a189 n49 n70 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {3, 9} {1, 2, 8} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c11439 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a189 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 7} {5, 8} {1, 2, 3} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c11442 (h : TenSystem T Q) :
    Q {0, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a189 n57 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 7} {5, 8} {1, 3, 9} a189 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c11463 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {5, 7, 9} → False := by
  intro a190 a37 a115
  have hc := h.complementary {0, 4, 6, 8} {1, 2, 3} a190 (by decide) (by decide)
  have he : ( {0, 4, 6, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a115

theorem c11465 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 5} → T {3, 7, 9} → False := by
  intro a190 a39 a99
  have hc := h.complementary {0, 4, 6, 8} {1, 2, 5} a190 (by decide) (by decide)
  have he : ( {0, 4, 6, 8} : Finset Labels)ᶜ \ {1, 2, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a39 a99

theorem c11478 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ T {1, 5, 9} → ¬ T {2, 3, 7} → False := by
  intro a190 n58 n68
  have hc := h.complementary {0, 4, 6, 8} {1, 5, 9} a190 (by decide) (by decide)
  have he : ( {0, 4, 6, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n58 (hc.mpr n68)

theorem c11483 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a190 a37 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 2} {3, 5, 7} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c11485 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a190 a37 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 2} {3, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11487 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a190 a37 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 2} {3, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11493 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a190 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 3} {2, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11495 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a190 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 3} {2, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11505 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a190 a45 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 5} {3, 7, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c11513 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 3, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a190 a47 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 7} {3, 5, 9} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

theorem c11515 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 5, 9} → False := by
  intro a190 a43 a49 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {1, 9} {2, 3, 5} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)

theorem c11547 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 9} → T {2, 3, 9} → T {2, 5, 9} → False := by
  intro a190 a43 a70 a79
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {2, 9} {1, 3, 5} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)

theorem c11551 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → T {1, 2, 9} → T {2, 5, 9} → T {2, 7, 9} → False := by
  intro a190 a43 a79 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 8} {2, 9} {1, 5, 7} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c11572 (h : TenSystem T Q) :
    Q {0, 4, 6, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 7, 9} → False := by
  intro a190 n49 n70 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 8} {3, 9} {1, 2, 7} a190 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) ht)

theorem c11606 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 2, 7} → ¬ T {3, 5, 8} → False := by
  intro a191 n41 n93
  have hc := h.complementary {0, 4, 6, 9} {1, 2, 7} a191 (by decide) (by decide)
  have he : ( {0, 4, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n93)

theorem c11613 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → T {1, 3, 7} → T {2, 5, 8} → False := by
  intro a191 a47 a78
  have hc := h.complementary {0, 4, 6, 9} {1, 3, 7} a191 (by decide) (by decide)
  have he : ( {0, 4, 6, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a47 a78

theorem c11618 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 5, 8} → ¬ T {2, 3, 7} → False := by
  intro a191 n57 n68
  have hc := h.complementary {0, 4, 6, 9} {1, 5, 8} a191 (by decide) (by decide)
  have he : ( {0, 4, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n68)

theorem c11619 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → T {1, 5, 8} → T {2, 3, 7} → False := by
  intro a191 a57 a68
  have hc := h.complementary {0, 4, 6, 9} {1, 5, 8} a191 (by decide) (by decide)
  have he : ( {0, 4, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a68

theorem c11696 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 3, 5} → ¬ T {2, 3, 5} → ¬ T {3, 5, 8} → False := by
  intro a191 n45 n66 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 9} {3, 5} {1, 2, 8} a191 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 5} = {2, 3, 5} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c11722 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 8} → False := by
  intro a191 n56 n92 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 6, 9} {5, 7} {1, 3, 8} a191 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c11727 (h : TenSystem T Q) :
    Q {0, 4, 6, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a191 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 6, 9} {5, 8} {1, 2, 3} a191 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c11743 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {5, 6, 9} → False := by
  intro a192 a37 a113
  have hc := h.complementary {0, 4, 7, 8} {1, 2, 3} a192 (by decide) (by decide)
  have he : ( {0, 4, 7, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a113

theorem c11751 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 3, 5} → T {2, 6, 9} → False := by
  intro a192 a45 a82
  have hc := h.complementary {0, 4, 7, 8} {1, 3, 5} a192 (by decide) (by decide)
  have he : ( {0, 4, 7, 8} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a45 a82

theorem c11754 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {1, 3, 9} → ¬ T {2, 5, 6} → False := by
  intro a192 n49 n76
  have hc := h.complementary {0, 4, 7, 8} {1, 3, 9} a192 (by decide) (by decide)
  have he : ( {0, 4, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n76)

theorem c11755 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 3, 9} → T {2, 5, 6} → False := by
  intro a192 a49 a76
  have hc := h.complementary {0, 4, 7, 8} {1, 3, 9} a192 (by decide) (by decide)
  have he : ( {0, 4, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a49 a76

theorem c11767 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a192 a37 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {1, 2} {3, 6, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c11773 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a192 a37 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {1, 3} {2, 5, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11775 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a192 a37 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {1, 3} {2, 6, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c11807 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 9} → False := by
  intro a192 a37 a67 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {2, 3} {1, 6, 9} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c11851 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 5, 9} → False := by
  intro a192 a49 a70 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {3, 9} {1, 2, 5} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)

theorem c11852 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 6, 9} → False := by
  intro a192 n49 n70 n97
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 8} {3, 9} {1, 2, 6} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) ht)

theorem c11859 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 5, 6} → T {2, 5, 6} → T {3, 5, 6} → False := by
  intro a192 a55 a76 a91
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {5, 6} {1, 2, 3} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)

end BorsukNine.FiniteObstruction

end OAI
