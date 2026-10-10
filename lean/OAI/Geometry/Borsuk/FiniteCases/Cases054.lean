import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18851 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 3, 9} → T {2, 3, 9} → T {3, 6, 9} → False := by
  intro a242 a21 a70 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {3, 9} {0, 2, 6} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c18862 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → ¬ T {0, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a242 n32 n96 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 7} {6, 8} {0, 3, 9} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n32 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c18875 (h : TenSystem T Q) :
    Q {1, 4, 5, 7} → T {0, 8, 9} → T {2, 8, 9} → T {3, 8, 9} → False := by
  intro a242 a36 a85 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 7} {8, 9} {0, 2, 3} a242 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) a85)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)

theorem c18889 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {3, 6, 7} → False := by
  intro a243 a15 a95
  have hc := h.complementary {1, 4, 5, 8} {0, 2, 9} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a95

theorem c18894 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 3, 9} → ¬ T {2, 6, 7} → False := by
  intro a243 n21 n80
  have hc := h.complementary {1, 4, 5, 8} {0, 3, 9} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n80)

theorem c18896 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {2, 3, 9} → False := by
  intro a243 n31 n70
  have hc := h.complementary {1, 4, 5, 8} {0, 6, 7} a243 (by decide) (by decide)
  have he : ( {1, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n70)

theorem c18903 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a243 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 2} {3, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c18913 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a243 a9 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 3} {2, 6, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c18915 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a243 a9 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 3} {2, 7, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c18937 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a243 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {0, 9} {2, 3, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c18943 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 3} → T {2, 3, 6} → T {2, 3, 7} → False := by
  intro a243 a9 a67 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {2, 3} {0, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

theorem c18954 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 6} → ¬ T {2, 6, 7} → ¬ T {2, 6, 9} → False := by
  intro a243 n12 n80 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 6} {0, 7, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 6} = {2, 6, 9} by decide)) ht)

theorem c18958 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a243 n13 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 7} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c18962 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 7} → ¬ T {2, 6, 7} → ¬ T {2, 7, 9} → False := by
  intro a243 n13 n80 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 7} {0, 6, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n13 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c18966 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 6, 9} → False := by
  intro a243 n15 n70 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {2, 9} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c18969 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 2, 9} → T {2, 3, 9} → T {2, 7, 9} → False := by
  intro a243 a15 a70 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {2, 9} {0, 3, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c18991 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 3, 9} → T {2, 3, 9} → T {3, 6, 9} → False := by
  intro a243 a21 a70 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {0, 2, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)

theorem c18995 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {0, 3, 9} → T {3, 6, 9} → T {3, 7, 9} → False := by
  intro a243 a21 a97 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {0, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c18997 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → T {2, 3, 9} → T {3, 6, 9} → T {3, 7, 9} → False := by
  intro a243 a70 a97 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 8} {3, 9} {2, 6, 7} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c19000 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {2, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n31 n80 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {0, 2, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19002 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n31 n95 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {0, 3, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19004 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {2, 6, 7} → ¬ T {3, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a243 n80 n95 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {6, 7} {2, 3, 9} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c19018 (h : TenSystem T Q) :
    Q {1, 4, 5, 8} → ¬ T {0, 7, 9} → ¬ T {3, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a243 n35 n99 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 5, 8} {7, 9} {0, 3, 6} a243 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n35 (Eq.mp (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)

theorem c19023 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {6, 7, 8} → False := by
  intro a244 a9 a117
  have hc := h.complementary {1, 4, 5, 9} {0, 2, 3} a244 (by decide) (by decide)
  have he : ( {1, 4, 5, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a117

theorem c19043 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a244 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {0, 2} {3, 6, 7} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19055 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a244 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {0, 3} {2, 7, 8} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19091 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 6} → T {2, 3, 6} → T {2, 6, 7} → False := by
  intro a244 a12 a67 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {2, 6} {0, 3, 7} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

theorem c19099 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 2, 7} → T {2, 3, 7} → T {2, 6, 7} → False := by
  intro a244 a13 a68 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {2, 7} {0, 3, 6} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) a80)

theorem c19139 (h : TenSystem T Q) :
    Q {1, 4, 5, 9} → T {0, 6, 7} → T {2, 6, 7} → T {3, 6, 7} → False := by
  intro a244 a31 a80 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 5, 9} {6, 7} {0, 2, 3} a244 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) a80)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c19163 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {5, 8, 9} → False := by
  intro a245 a9 a116
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 3} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a116

theorem c19165 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 5} → T {3, 8, 9} → False := by
  intro a245 a11 a100
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 5} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a11 a100

theorem c19167 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 8} → T {3, 5, 9} → False := by
  intro a245 a14 a94
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 8} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a14 a94

theorem c19169 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 9} → T {3, 5, 8} → False := by
  intro a245 a15 a93
  have hc := h.complementary {1, 4, 6, 7} {0, 2, 9} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a93

theorem c19175 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 3, 9} → T {2, 5, 8} → False := by
  intro a245 a21 a78
  have hc := h.complementary {1, 4, 6, 7} {0, 3, 9} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a78

theorem c19176 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {2, 3, 9} → False := by
  intro a245 n29 n70
  have hc := h.complementary {1, 4, 6, 7} {0, 5, 8} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n70)

theorem c19177 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 5, 8} → T {2, 3, 9} → False := by
  intro a245 a29 a70
  have hc := h.complementary {1, 4, 6, 7} {0, 5, 8} a245 (by decide) (by decide)
  have he : ( {1, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a70

theorem c19183 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 8} → False := by
  intro a245 a9 a11 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {0, 2} {3, 5, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c19191 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a245 a9 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {0, 3} {2, 5, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19225 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 9} → False := by
  intro a245 a9 a66 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {2, 3} {0, 5, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c19227 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 2, 3} → T {2, 3, 8} → T {2, 3, 9} → False := by
  intro a245 a9 a69 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {2, 3} {0, 8, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 3} = {2, 3, 8} by decide)) a69)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c19246 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 5, 9} → False := by
  intro a245 n15 n70 n79
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {2, 9} {0, 3, 5} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n79 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) ht)

theorem c19248 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 2, 9} → ¬ T {2, 3, 9} → ¬ T {2, 8, 9} → False := by
  intro a245 n15 n70 n85
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {2, 9} {0, 3, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) ht)
  · exact n85 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) ht)

theorem c19272 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 8, 9} → False := by
  intro a245 n21 n70 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {3, 9} {0, 2, 8} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c19279 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → T {0, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a245 a29 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 7} {5, 8} {0, 2, 3} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c19280 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a245 n29 n78 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {5, 8} {0, 2, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
