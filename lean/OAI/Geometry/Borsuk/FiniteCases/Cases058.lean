import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c20828 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n24 n73 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {4, 7} {0, 2, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c20830 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n24 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {4, 7} {0, 3, 6} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c20838 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n31 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {6, 7} {0, 3, 4} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c20840 (h : TenSystem T Q) :
    Q {1, 5, 8, 9} → ¬ T {2, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a256 n80 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 8, 9} {6, 7} {2, 3, 4} a256 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c20850 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 3, 4} → ¬ T {2, 5, 9} → False := by
  intro a257 n16 n79
  have hc := h.complementary {1, 6, 7, 8} {0, 3, 4} a257 (by decide) (by decide)
  have he : ( {1, 6, 7, 8} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 5, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n79)

theorem c20856 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 4, 5} → ¬ T {2, 3, 9} → False := by
  intro a257 n22 n70
  have hc := h.complementary {1, 6, 7, 8} {0, 4, 5} a257 (by decide) (by decide)
  have he : ( {1, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n70)

theorem c20858 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 4, 9} → ¬ T {2, 3, 5} → False := by
  intro a257 n26 n66
  have hc := h.complementary {1, 6, 7, 8} {0, 4, 9} a257 (by decide) (by decide)
  have he : ( {1, 6, 7, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n66)

theorem c20868 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 2, 5} → ¬ T {0, 2, 9} → False := by
  intro a257 n10 n11 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 8} {0, 2} {4, 5, 9} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c20878 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a257 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 8} {0, 4} {2, 3, 5} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c20895 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a257 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 8} {0, 9} {2, 3, 4} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c20957 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → T {2, 3, 9} → T {3, 4, 9} → T {3, 5, 9} → False := by
  intro a257 a70 a90 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 8} {3, 9} {2, 4, 5} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)

theorem c20967 (h : TenSystem T Q) :
    Q {1, 6, 7, 8} → T {0, 4, 9} → T {2, 4, 9} → T {3, 4, 9} → False := by
  intro a257 a26 a75 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 8} {4, 9} {0, 2, 3} a257 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)

theorem c20983 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 2, 3} → T {4, 5, 8} → False := by
  intro a258 a9 a103
  have hc := h.complementary {1, 6, 7, 9} {0, 2, 3} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a103

theorem c20990 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 3, 4} → ¬ T {2, 5, 8} → False := by
  intro a258 n16 n78
  have hc := h.complementary {1, 6, 7, 9} {0, 3, 4} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n78)

theorem c20995 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 3, 8} → T {2, 4, 5} → False := by
  intro a258 a20 a71
  have hc := h.complementary {1, 6, 7, 9} {0, 3, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a20 a71

theorem c21000 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 3, 4} → False := by
  intro a258 n29 n65
  have hc := h.complementary {1, 6, 7, 9} {0, 5, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n65)

theorem c21001 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 5, 8} → T {2, 3, 4} → False := by
  intro a258 a29 a65
  have hc := h.complementary {1, 6, 7, 9} {0, 5, 8} a258 (by decide) (by decide)
  have he : ( {1, 6, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a29 a65

theorem c21018 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a258 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {0, 4} {2, 3, 5} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c21022 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 2, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 8} → False := by
  intro a258 n10 n22 n25
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {0, 4} {2, 5, 8} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n25 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 4} = {0, 4, 8} by decide)) ht)

theorem c21039 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 2, 8} → T {0, 4, 8} → T {0, 5, 8} → False := by
  intro a258 a14 a25 a29
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 9} {0, 8} {2, 4, 5} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)

theorem c21100 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 4, 5} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a258 n22 n71 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {4, 5} {0, 2, 8} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c21104 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {2, 4, 5} → ¬ T {3, 4, 5} → ¬ T {4, 5, 8} → False := by
  intro a258 n71 n86 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {4, 5} {2, 3, 8} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n86 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c21115 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → T {0, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a258 a29 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 7, 9} {5, 8} {0, 2, 3} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c21118 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a258 n29 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {5, 8} {0, 3, 4} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c21120 (h : TenSystem T Q) :
    Q {1, 6, 7, 9} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a258 n78 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 7, 9} {5, 8} {2, 3, 4} a258 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c21123 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 3} → T {4, 5, 7} → False := by
  intro a259 a9 a102
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 3} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a9 a102

theorem c21124 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {3, 5, 7} → False := by
  intro a259 n10 n92
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 4} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n92)

theorem c21126 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 5} → ¬ T {3, 4, 7} → False := by
  intro a259 n11 n88
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n88)

theorem c21128 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 7} → ¬ T {3, 4, 5} → False := by
  intro a259 n13 n86
  have hc := h.complementary {1, 6, 8, 9} {0, 2, 7} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {3, 4, 5} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n86)

theorem c21132 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 5} → ¬ T {2, 4, 7} → False := by
  intro a259 n17 n73
  have hc := h.complementary {1, 6, 8, 9} {0, 3, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n73)

theorem c21133 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 3, 5} → T {2, 4, 7} → False := by
  intro a259 a17 a73
  have hc := h.complementary {1, 6, 8, 9} {0, 3, 5} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a17 a73

theorem c21139 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 4, 7} → T {2, 3, 5} → False := by
  intro a259 a24 a66
  have hc := h.complementary {1, 6, 8, 9} {0, 4, 7} a259 (by decide) (by decide)
  have he : ( {1, 6, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 5} := by decide
  rw [he] at hc
  exact hc.mp a24 a66

theorem c21143 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 5} → False := by
  intro a259 a9 a10 a11
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {0, 2} {3, 4, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)

theorem c21145 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a259 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {0, 2} {3, 4, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c21158 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {0, 3, 4} → ¬ T {0, 4, 5} → False := by
  intro a259 n10 n16 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {0, 4} {2, 3, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 4} = {0, 2, 4} by decide)) ht)
  · exact n16 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 4} = {0, 3, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)

theorem c21192 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a259 n10 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {2, 4} {0, 3, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c21195 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 2, 4} → T {2, 4, 5} → T {2, 4, 7} → False := by
  intro a259 a10 a71 a73
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {2, 4} {0, 5, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)

theorem c21214 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 5} → False := by
  intro a259 n16 n65 n86
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 4} {0, 2, 5} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n86 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) ht)

theorem c21216 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 7} → False := by
  intro a259 n16 n65 n88
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 4} {0, 2, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) ht)

theorem c21222 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 5} → ¬ T {2, 3, 5} → ¬ T {3, 4, 5} → False := by
  intro a259 n17 n66 n86
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 5} {0, 2, 4} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 5} = {2, 3, 5} by decide)) ht)
  · exact n86 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) ht)

theorem c21224 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → ¬ T {0, 3, 5} → ¬ T {2, 3, 5} → ¬ T {3, 5, 7} → False := by
  intro a259 n17 n66 n92
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 6, 8, 9} {3, 5} {0, 2, 7} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 5} = {2, 3, 5} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 5} = {3, 5, 7} by decide)) ht)

theorem c21247 (h : TenSystem T Q) :
    Q {1, 6, 8, 9} → T {0, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a259 a24 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 6, 8, 9} {4, 7} {0, 2, 3} a259 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c21263 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {0, 2, 3} → T {4, 5, 6} → False := by
  intro a260 a9 a101
  have hc := h.complementary {1, 7, 8, 9} {0, 2, 3} a260 (by decide) (by decide)
  have he : ( {1, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a9 a101

theorem c21269 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → T {0, 2, 6} → T {3, 4, 5} → False := by
  intro a260 a12 a86
  have hc := h.complementary {1, 7, 8, 9} {0, 2, 6} a260 (by decide) (by decide)
  have he : ( {1, 7, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a12 a86

theorem c21306 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → ¬ T {0, 4, 5} → False := by
  intro a260 n11 n17 n22
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 7, 8, 9} {0, 5} {2, 3, 4} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)

theorem c21308 (h : TenSystem T Q) :
    Q {1, 7, 8, 9} → ¬ T {0, 2, 5} → ¬ T {0, 3, 5} → ¬ T {0, 5, 6} → False := by
  intro a260 n11 n17 n27
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 7, 8, 9} {0, 5} {2, 3, 6} a260 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) ht)
  · exact n17 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) ht)
  · exact n27 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 5} = {0, 5, 6} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
