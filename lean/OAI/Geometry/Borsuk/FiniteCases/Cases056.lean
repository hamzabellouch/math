import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c19943 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 6} → T {2, 5, 6} → T {2, 6, 7} → False := by
  intro a250 a12 a76 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 6} {0, 5, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c19949 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 7} → T {2, 3, 7} → T {2, 6, 7} → False := by
  intro a250 a13 a68 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 7} {0, 3, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c19951 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 7} → T {2, 5, 7} → T {2, 6, 7} → False := by
  intro a250 a13 a77 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 7} {0, 5, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 7} = {2, 5, 7} by decide)) a77)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c19980 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a250 n27 n76 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 8, 9} {5, 6} {0, 2, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c19982 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 7} → False := by
  intro a250 n27 n91 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 8, 9} {5, 6} {0, 3, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)

theorem c19995 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 6, 7} → T {2, 6, 7} → T {3, 6, 7} → False := by
  intro a250 a31 a80 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {6, 7} {0, 2, 3} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c20003 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 3} → T {4, 8, 9} → False := by
  intro a251 a9 a110
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 3} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a110

theorem c20004 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {3, 8, 9} → False := by
  intro a251 n10 n100
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 4} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n100)

theorem c20008 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 9} → ¬ T {3, 4, 8} → False := by
  intro a251 n15 n89
  have hc := h.complementary {1, 5, 6, 7} {0, 2, 9} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 4, 8} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n89)

theorem c20010 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 3, 4} → ¬ T {2, 8, 9} → False := by
  intro a251 n16 n85
  have hc := h.complementary {1, 5, 6, 7} {0, 3, 4} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 8, 9} := by decide
  rw [he] at hc
  exact n16 (hc.mpr n85)

theorem c20016 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 4, 8} → ¬ T {2, 3, 9} → False := by
  intro a251 n25 n70
  have hc := h.complementary {1, 5, 6, 7} {0, 4, 8} a251 (by decide) (by decide)
  have he : ( {1, 5, 6, 7} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n70)

theorem c20025 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 9} → False := by
  intro a251 a9 a10 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {0, 2} {3, 4, 9} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c20028 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → ¬ T {0, 2, 4} → ¬ T {0, 2, 8} → ¬ T {0, 2, 9} → False := by
  intro a251 n10 n14 n15
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 7} {0, 2} {4, 8, 9} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)
  · exact n15 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) ht)

theorem c20055 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 2, 9} → T {0, 3, 9} → T {0, 4, 9} → False := by
  intro a251 a15 a21 a26
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {0, 9} {2, 3, 4} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)

theorem c20117 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {2, 3, 9} → T {3, 4, 9} → T {3, 8, 9} → False := by
  intro a251 a70 a90 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {3, 9} {2, 4, 8} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c20127 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 4, 9} → T {2, 4, 9} → T {3, 4, 9} → False := by
  intro a251 a26 a75 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {4, 9} {0, 2, 3} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)

theorem c20135 (h : TenSystem T Q) :
    Q {1, 5, 6, 7} → T {0, 8, 9} → T {2, 8, 9} → T {3, 8, 9} → False := by
  intro a251 a36 a85 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 7} {8, 9} {0, 2, 3} a251 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) a85)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)

theorem c20143 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {4, 7, 9} → False := by
  intro a252 a9 a109
  have hc := h.complementary {1, 5, 6, 8} {0, 2, 3} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a109

theorem c20149 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 9} → T {3, 4, 7} → False := by
  intro a252 a15 a88
  have hc := h.complementary {1, 5, 6, 8} {0, 2, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a88

theorem c20151 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 4} → T {2, 7, 9} → False := by
  intro a252 a16 a84
  have hc := h.complementary {1, 5, 6, 8} {0, 3, 4} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a16 a84

theorem c20154 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 3, 9} → ¬ T {2, 4, 7} → False := by
  intro a252 n21 n73
  have hc := h.complementary {1, 5, 6, 8} {0, 3, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n73)

theorem c20155 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {2, 4, 7} → False := by
  intro a252 a21 a73
  have hc := h.complementary {1, 5, 6, 8} {0, 3, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a21 a73

theorem c20156 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {2, 3, 9} → False := by
  intro a252 n24 n70
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 7} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n70)

theorem c20157 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 4, 7} → T {2, 3, 9} → False := by
  intro a252 a24 a70
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 7} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a70

theorem c20158 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 9} → ¬ T {2, 3, 7} → False := by
  intro a252 n26 n68
  have hc := h.complementary {1, 5, 6, 8} {0, 4, 9} a252 (by decide) (by decide)
  have he : ( {1, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 9} = {2, 3, 7} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n68)

theorem c20163 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a252 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {0, 2} {3, 4, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c20205 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a252 a9 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {2, 3} {0, 4, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c20207 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 2, 3} → T {2, 3, 7} → T {2, 3, 9} → False := by
  intro a252 a9 a68 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {2, 3} {0, 7, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c20220 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 7, 9} → False := by
  intro a252 n13 n68 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {2, 7} {0, 3, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c20226 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 4, 9} → False := by
  intro a252 n15 n70 n75
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {2, 9} {0, 3, 4} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)

theorem c20228 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 7, 9} → False := by
  intro a252 n15 n70 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {2, 9} {0, 3, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) ht)

theorem c20234 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 7} → False := by
  intro a252 n16 n65 n88
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {3, 4} {0, 2, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) ht)

theorem c20236 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a252 n16 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {3, 4} {0, 2, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n16 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 4} = {0, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c20251 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {2, 3, 9} → T {3, 4, 9} → False := by
  intro a252 a21 a70 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {3, 9} {0, 2, 4} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)

theorem c20255 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 3, 9} → T {3, 4, 9} → T {3, 7, 9} → False := by
  intro a252 a21 a90 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {3, 9} {0, 4, 7} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c20259 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → T {0, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a252 a24 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 8} {4, 7} {0, 2, 3} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c20260 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a252 n24 n73 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {4, 7} {0, 2, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c20262 (h : TenSystem T Q) :
    Q {1, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a252 n24 n88 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 8} {4, 7} {0, 3, 9} a252 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c20283 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 2, 3} → T {4, 7, 8} → False := by
  intro a253 a9 a108
  have hc := h.complementary {1, 5, 6, 9} {0, 2, 3} a253 (by decide) (by decide)
  have he : ( {1, 5, 6, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a108

theorem c20288 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 2, 8} → ¬ T {3, 4, 7} → False := by
  intro a253 n14 n88
  have hc := h.complementary {1, 5, 6, 9} {0, 2, 8} a253 (by decide) (by decide)
  have he : ( {1, 5, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n88)

theorem c20294 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 3, 8} → ¬ T {2, 4, 7} → False := by
  intro a253 n20 n73
  have hc := h.complementary {1, 5, 6, 9} {0, 3, 8} a253 (by decide) (by decide)
  have he : ( {1, 5, 6, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n73)

theorem c20303 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 2, 3} → T {0, 2, 4} → T {0, 2, 7} → False := by
  intro a253 a9 a10 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 9} {0, 2} {3, 4, 7} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 2} = {0, 2, 4} by decide)) a10)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c20315 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a253 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 9} {0, 3} {2, 7, 8} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c20350 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → ¬ T {0, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a253 n10 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 5, 6, 9} {2, 4} {0, 3, 7} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n10 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 4} = {0, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c20399 (h : TenSystem T Q) :
    Q {1, 5, 6, 9} → T {0, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a253 a24 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 5, 6, 9} {4, 7} {0, 2, 3} a253 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c20425 (h : TenSystem T Q) :
    Q {1, 5, 7, 8} → T {0, 2, 4} → T {3, 6, 9} → False := by
  intro a254 a10 a97
  have hc := h.complementary {1, 5, 7, 8} {0, 2, 4} a254 (by decide) (by decide)
  have he : ( {1, 5, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {3, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a10 a97

end BorsukNine.FiniteObstruction

end OAI
