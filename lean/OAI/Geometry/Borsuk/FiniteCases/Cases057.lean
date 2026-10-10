import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c20427 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 6} → T {3, 4, 9} → False := by
  intro a254 a12 a90
  have hc := h.complementary {1, 5, 7, 8} {0, 2, 6} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a12 a90

theorem c20431 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 3, 4} → T {2, 6, 9} → False := by
  intro a254 a16 a82
  have hc := h.complementary {1, 5, 7, 8} {0, 3, 4} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a16 a82

theorem c20434 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 3, 9} → ¬ T {2, 4, 6} → False := by
  intro a254 n21 n72
  have hc := h.complementary {1, 5, 7, 8} {0, 3, 9} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n72)

theorem c20436 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {2, 3, 9} → False := by
  intro a254 n23 n70
  have hc := h.complementary {1, 5, 7, 8} {0, 4, 6} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n70)

theorem c20437 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 4, 6} → T {2, 3, 9} → False := by
  intro a254 a23 a70
  have hc := h.complementary {1, 5, 7, 8} {0, 4, 6} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a70

theorem c20445 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a254 a9 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 2} {3, 4, 9} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c20448 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 6} → ¬ T {0, 2, 9} → False := by
  intro a254 n10 n12 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 8} {0, 2} {4, 6, 9} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c20451 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a254 a9 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 3} {2, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c20475 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a254 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 9} {2, 3, 4} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c20479 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a254 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {0, 9} {2, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c20483 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a254 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {2, 3} {0, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20500 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 6, 9} → False := by
  intro a254 n12 n67 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 8} {2, 6} {0, 3, 9} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) ht)

theorem c20507 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 9} → T {2, 3, 9} → T {2, 4, 9} → False := by
  intro a254 a15 a70 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 8} {2, 9} {0, 3, 4} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)

theorem c20510 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a254 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 8} {2, 9} {0, 4, 6} a254 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c20563 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 3} → T {4, 6, 8} → False := by
  intro a255 a9 a106
  have hc := h.complementary {1, 5, 7, 9} {0, 2, 3} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a106

theorem c20567 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 6} → T {3, 4, 8} → False := by
  intro a255 a12 a89
  have hc := h.complementary {1, 5, 7, 9} {0, 2, 6} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a89

theorem c20571 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 3, 4} → T {2, 6, 8} → False := by
  intro a255 a16 a81
  have hc := h.complementary {1, 5, 7, 9} {0, 3, 4} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a16 a81

theorem c20575 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 3, 8} → T {2, 4, 6} → False := by
  intro a255 a20 a72
  have hc := h.complementary {1, 5, 7, 9} {0, 3, 8} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a20 a72

theorem c20581 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 6, 8} → T {2, 3, 4} → False := by
  intro a255 a32 a65
  have hc := h.complementary {1, 5, 7, 9} {0, 6, 8} a255 (by decide) (by decide)
  have he : ( {1, 5, 7, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a32 a65

theorem c20623 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a255 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 9} {2, 3} {0, 4, 6} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20630 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 6} → False := by
  intro a255 n10 n65 n72
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 9} {2, 4} {0, 3, 6} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) ht)

theorem c20679 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → T {0, 4, 6} → T {2, 4, 6} → T {3, 4, 6} → False := by
  intro a255 a23 a72 a87
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 7, 9} {4, 6} {0, 2, 3} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)

theorem c20698 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a255 n32 n96 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 9} {6, 8} {0, 3, 4} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)

theorem c20700 (h : TenSystem T Q) :
    Q {1, 5, 7, 9} → ¬ T {2, 6, 8} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → False := by
  intro a255 n81 n96 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 7, 9} {6, 8} {2, 3, 4} a255 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n81 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)

theorem c20703 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {4, 6, 7} → False := by
  intro a256 a9 a105
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 3} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a9 a105

theorem c20704 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 2, 4} → ¬ T {3, 6, 7} → False := by
  intro a256 n10 n95
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 4} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 6, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n95)

theorem c20705 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 4} → T {3, 6, 7} → False := by
  intro a256 a10 a95
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 4} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a10 a95

theorem c20707 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 6} → T {3, 4, 7} → False := by
  intro a256 a12 a88
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a88

theorem c20709 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 7} → T {3, 4, 6} → False := by
  intro a256 a13 a87
  have hc := h.complementary {1, 5, 8, 9} {0, 2, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a87

theorem c20713 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 3, 6} → T {2, 4, 7} → False := by
  intro a256 a18 a73
  have hc := h.complementary {1, 5, 8, 9} {0, 3, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a18 a73

theorem c20716 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 6} → ¬ T {2, 3, 7} → False := by
  intro a256 n23 n68
  have hc := h.complementary {1, 5, 8, 9} {0, 4, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n68)

theorem c20717 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 4, 6} → T {2, 3, 7} → False := by
  intro a256 a23 a68
  have hc := h.complementary {1, 5, 8, 9} {0, 4, 6} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a23 a68

theorem c20718 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 3, 6} → False := by
  intro a256 n24 n67
  have hc := h.complementary {1, 5, 8, 9} {0, 4, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n67)

theorem c20719 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 4, 7} → T {2, 3, 6} → False := by
  intro a256 a24 a67
  have hc := h.complementary {1, 5, 8, 9} {0, 4, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a24 a67

theorem c20720 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {2, 3, 4} → False := by
  intro a256 n31 n65
  have hc := h.complementary {1, 5, 8, 9} {0, 6, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n65)

theorem c20721 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 6, 7} → T {2, 3, 4} → False := by
  intro a256 a31 a65
  have hc := h.complementary {1, 5, 8, 9} {0, 6, 7} a256 (by decide) (by decide)
  have he : ( {1, 5, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a31 a65

theorem c20727 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a256 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 2} {3, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c20731 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a256 a9 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 3} {2, 4, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c20735 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {0, 3, 6} → T {0, 3, 7} → False := by
  intro a256 a9 a18 a19
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 3} {2, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)

theorem c20743 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 4} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a256 a10 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {0, 4} {2, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c20752 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 3, 6} → ¬ T {0, 4, 6} → ¬ T {0, 6, 7} → False := by
  intro a256 n18 n23 n31
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {0, 6} {3, 4, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n23 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) ht)
  · exact n31 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) ht)

theorem c20763 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 6} → False := by
  intro a256 a9 a65 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {2, 3} {0, 4, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c20767 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → T {0, 2, 3} → T {2, 3, 6} → T {2, 3, 7} → False := by
  intro a256 a9 a67 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 8, 9} {2, 3} {0, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

theorem c20768 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {2, 3, 4} → ¬ T {2, 3, 6} → ¬ T {2, 3, 7} → False := by
  intro a256 n65 n67 n68
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {2, 3} {4, 6, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n65 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) ht)

theorem c20772 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a256 n10 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {2, 4} {0, 3, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c20804 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 7} → False := by
  intro a256 n18 n67 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {3, 6} {0, 2, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 6} = {0, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c20808 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {2, 3, 6} → ¬ T {3, 4, 6} → ¬ T {3, 6, 7} → False := by
  intro a256 n67 n87 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {3, 6} {2, 4, 7} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
