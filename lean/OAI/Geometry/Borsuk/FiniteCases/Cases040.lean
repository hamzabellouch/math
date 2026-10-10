import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c11875 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → T {1, 6, 9} → T {2, 6, 9} → T {3, 6, 9} → False := by
  intro a192 a61 a82 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 8} {6, 9} {1, 2, 3} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)

theorem c11880 (h : TenSystem T Q) :
    Q {0, 4, 7, 8} → ¬ T {2, 6, 9} → ¬ T {3, 6, 9} → ¬ T {5, 6, 9} → False := by
  intro a192 n82 n97 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 8} {6, 9} {2, 3, 5} a192 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n82 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) ht)
  · exact n97 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)

theorem c11883 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {5, 6, 8} → False := by
  intro a193 a37 a112
  have hc := h.complementary {0, 4, 7, 9} {1, 2, 3} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a112

theorem c11886 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 2, 6} → ¬ T {3, 5, 8} → False := by
  intro a193 n40 n93
  have hc := h.complementary {0, 4, 7, 9} {1, 2, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n93)

theorem c11890 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 5} → ¬ T {2, 6, 8} → False := by
  intro a193 n45 n81
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 5} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n81)

theorem c11892 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 5, 8} → False := by
  intro a193 n46 n78
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n46 (hc.mpr n78)

theorem c11893 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 3, 6} → T {2, 5, 8} → False := by
  intro a193 a46 a78
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 6} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a78

theorem c11894 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 8} → ¬ T {2, 5, 6} → False := by
  intro a193 n48 n76
  have hc := h.complementary {0, 4, 7, 9} {1, 3, 8} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n48 (hc.mpr n76)

theorem c11898 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 5, 8} → ¬ T {2, 3, 6} → False := by
  intro a193 n57 n67
  have hc := h.complementary {0, 4, 7, 9} {1, 5, 8} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n67)

theorem c11899 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 5, 8} → T {2, 3, 6} → False := by
  intro a193 a57 a67
  have hc := h.complementary {0, 4, 7, 9} {1, 5, 8} a193 (by decide) (by decide)
  have he : ( {0, 4, 7, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a57 a67

theorem c11903 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a193 a37 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 2} {3, 5, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c11911 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a193 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 3} {2, 5, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c11915 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 8} → False := by
  intro a193 a37 a46 a48
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 3} {2, 6, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)

theorem c11930 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 2, 6} → ¬ T {1, 5, 6} → ¬ T {1, 6, 8} → False := by
  intro a193 n40 n55 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {1, 6} {2, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

theorem c11932 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {1, 5, 6} → ¬ T {1, 6, 8} → False := by
  intro a193 n46 n55 n60
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {1, 6} {3, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n55 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) ht)
  · exact n60 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) ht)

theorem c11933 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 3, 6} → T {1, 5, 6} → T {1, 6, 8} → False := by
  intro a193 a46 a55 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {1, 6} {3, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) a60)

theorem c11963 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 8} → False := by
  intro a193 a40 a76 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {2, 6} {1, 5, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

theorem c11982 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 5, 6} → False := by
  intro a193 n46 n67 n91
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {3, 6} {1, 2, 5} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) ht)

theorem c11984 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 8} → False := by
  intro a193 n46 n67 n96
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {3, 6} {1, 2, 8} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) ht)

theorem c12007 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a193 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 7, 9} {5, 8} {1, 2, 3} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c12010 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a193 n57 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {5, 8} {1, 3, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c12012 (h : TenSystem T Q) :
    Q {0, 4, 7, 9} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a193 n78 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 7, 9} {5, 8} {2, 3, 6} a193 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c12023 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {5, 6, 7} → False := by
  intro a194 a37 a111
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 3} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a111

theorem c12026 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 6} → ¬ T {3, 5, 7} → False := by
  intro a194 n40 n92
  have hc := h.complementary {0, 4, 8, 9} {1, 2, 6} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n92)

theorem c12031 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 5} → T {2, 6, 7} → False := by
  intro a194 a45 a80
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 5} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a45 a80

theorem c12033 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 6} → T {2, 5, 7} → False := by
  intro a194 a46 a77
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 6} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {2, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a46 a77

theorem c12035 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 3, 7} → T {2, 5, 6} → False := by
  intro a194 a47 a76
  have hc := h.complementary {0, 4, 8, 9} {1, 3, 7} a194 (by decide) (by decide)
  have he : ( {0, 4, 8, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a47 a76

theorem c12051 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a194 a37 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 5, 6} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c12053 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a194 a37 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 5, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12055 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a194 a37 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {1, 3} {2, 6, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12092 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 5} → ¬ T {2, 3, 5} → ¬ T {2, 5, 7} → False := by
  intro a194 n39 n66 n77
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 8, 9} {2, 5} {1, 3, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n39 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 5} = {1, 2, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 5} = {2, 3, 5} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 5} = {2, 5, 7} by decide)) ht)

theorem c12103 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a194 a40 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {2, 6} {1, 5, 7} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c12108 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a194 n41 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 4, 8, 9} {2, 7} {1, 3, 6} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c12139 (h : TenSystem T Q) :
    Q {0, 4, 8, 9} → T {1, 5, 6} → T {2, 5, 6} → T {3, 5, 6} → False := by
  intro a194 a55 a76 a91
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 4, 8, 9} {5, 6} {1, 2, 3} a194 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)

theorem c12163 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {4, 8, 9} → False := by
  intro a195 a37 a110
  have hc := h.complementary {0, 5, 6, 7} {1, 2, 3} a195 (by decide) (by decide)
  have he : ( {0, 5, 6, 7} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a110

theorem c12185 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a195 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 2} {3, 4, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12193 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a195 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 3} {2, 4, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12195 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a195 a37 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 3} {2, 8, 9} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12217 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 9} → T {1, 3, 9} → T {1, 8, 9} → False := by
  intro a195 a43 a49 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {1, 9} {2, 3, 8} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c12249 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → T {1, 2, 9} → T {2, 3, 9} → T {2, 8, 9} → False := by
  intro a195 a43 a70 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 7} {2, 9} {1, 3, 8} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c12270 (h : TenSystem T Q) :
    Q {0, 5, 6, 7} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a195 n49 n70 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 7} {3, 9} {1, 2, 4} a195 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c12303 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {4, 7, 9} → False := by
  intro a196 a37 a109
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 3} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a109

theorem c12305 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 4} → T {3, 7, 9} → False := by
  intro a196 a38 a99
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 4} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a99

theorem c12306 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 7} → ¬ T {3, 4, 9} → False := by
  intro a196 n41 n90
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 7} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {3, 4, 9} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n90)

theorem c12309 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 9} → T {3, 4, 7} → False := by
  intro a196 a43 a88
  have hc := h.complementary {0, 5, 6, 8} {1, 2, 9} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 2, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a43 a88

theorem c12310 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {2, 7, 9} → False := by
  intro a196 n44 n84
  have hc := h.complementary {0, 5, 6, 8} {1, 3, 4} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact n44 (hc.mpr n84)

end BorsukNine.FiniteObstruction

end OAI
