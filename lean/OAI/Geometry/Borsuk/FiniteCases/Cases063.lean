import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c23516 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 7, 8} → ¬ T {1, 3, 9} → False := by
  intro a276 n34 n49
  have hc := h.complementary {2, 4, 5, 6} {0, 7, 8} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 7, 8} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n34 (hc.mpr n49)

theorem c23521 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 8, 9} → T {1, 3, 7} → False := by
  intro a276 a36 a47
  have hc := h.complementary {2, 4, 5, 6} {0, 8, 9} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a36 a47

theorem c23531 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a276 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {0, 3} {1, 7, 8} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c23555 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a276 a8 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {0, 9} {1, 3, 7} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c23556 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 8, 9} → False := by
  intro a276 n8 n21 n36
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 6} {0, 9} {1, 3, 8} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n36 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) ht)

theorem c23565 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a276 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {1, 3} {0, 7, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23567 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a276 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 6} {1, 3} {0, 8, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23596 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 3, 7} → ¬ T {1, 3, 7} → ¬ T {3, 7, 9} → False := by
  intro a276 n19 n47 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 6} {3, 7} {0, 1, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n19 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 7} = {0, 3, 7} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) ht)

theorem c23620 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 7, 8} → ¬ T {1, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a276 n34 n62 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 6} {7, 8} {0, 1, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n34 (Eq.mp (congrArg T (show insert (0 : Labels) {7, 8} = {0, 7, 8} by decide)) ht)
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c23622 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 7, 8} → ¬ T {3, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a276 n34 n98 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 6} {7, 8} {0, 3, 9} a276 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n34 (Eq.mp (congrArg T (show insert (0 : Labels) {7, 8} = {0, 7, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c23650 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {0, 3, 6} → ¬ T {1, 8, 9} → False := by
  intro a277 n18 n64
  have hc := h.complementary {2, 4, 5, 7} {0, 3, 6} a277 (by decide) (by decide)
  have he : ( {2, 4, 5, 7} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n64)

theorem c23673 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a277 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {0, 3} {1, 6, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23694 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 6, 9} → False := by
  intro a277 n8 n21 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 7} {0, 9} {1, 3, 6} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) ht)

theorem c23705 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a277 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {1, 3} {0, 6, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23707 (h : TenSystem T Q) :
    Q {2, 4, 5, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a277 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 7} {1, 3} {0, 8, 9} a277 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23796 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {0, 6, 7} → ¬ T {1, 3, 9} → False := by
  intro a278 n31 n49
  have hc := h.complementary {2, 4, 5, 8} {0, 6, 7} a278 (by decide) (by decide)
  have he : ( {2, 4, 5, 8} : Finset Labels)ᶜ \ {0, 6, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n49)

theorem c23813 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a278 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 6, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23815 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a278 a2 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {0, 3} {1, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c23820 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → ¬ T {0, 1, 6} → ¬ T {0, 3, 6} → ¬ T {0, 6, 9} → False := by
  intro a278 n5 n18 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 5, 8} {0, 6} {1, 3, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c23845 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a278 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {1, 3} {0, 6, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23847 (h : TenSystem T Q) :
    Q {2, 4, 5, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a278 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 8} {1, 3} {0, 7, 9} a278 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c23923 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 1, 3} → T {6, 7, 8} → False := by
  intro a279 a2 a117
  have hc := h.complementary {2, 4, 5, 9} {0, 1, 3} a279 (by decide) (by decide)
  have he : ( {2, 4, 5, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a117

theorem c23955 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a279 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {0, 3} {1, 7, 8} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c23983 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a279 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {1, 3} {0, 6, 7} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c24039 (h : TenSystem T Q) :
    Q {2, 4, 5, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a279 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 5, 9} {6, 7} {0, 1, 3} a279 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c24063 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {5, 8, 9} → False := by
  intro a280 a2 a116
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 3} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a116

theorem c24064 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 1, 5} → ¬ T {3, 8, 9} → False := by
  intro a280 n4 n100
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 5} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n100)

theorem c24068 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {3, 5, 8} → False := by
  intro a280 n8 n93
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n93)

theorem c24069 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 9} → T {3, 5, 8} → False := by
  intro a280 a8 a93
  have hc := h.complementary {2, 4, 6, 7} {0, 1, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a8 a93

theorem c24070 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {1, 8, 9} → False := by
  intro a280 n17 n64
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 5} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n64)

theorem c24071 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 3, 5} → T {1, 8, 9} → False := by
  intro a280 a17 a64
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 5} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a17 a64

theorem c24072 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 8} → ¬ T {1, 5, 9} → False := by
  intro a280 n20 n58
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 8} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 8} = {1, 5, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n58)

theorem c24073 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 3, 8} → T {1, 5, 9} → False := by
  intro a280 a20 a58
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 8} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 8} = {1, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a20 a58

theorem c24074 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {1, 5, 8} → False := by
  intro a280 n21 n57
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n57)

theorem c24075 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 3, 9} → T {1, 5, 8} → False := by
  intro a280 a21 a57
  have hc := h.complementary {2, 4, 6, 7} {0, 3, 9} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a57

theorem c24076 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 3, 9} → False := by
  intro a280 n29 n49
  have hc := h.complementary {2, 4, 6, 7} {0, 5, 8} a280 (by decide) (by decide)
  have he : ( {2, 4, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n49)

theorem c24085 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 9} → False := by
  intro a280 a2 a4 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 1} {3, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c24087 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 1, 8} → T {0, 1, 9} → False := by
  intro a280 a2 a7 a8
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 1} {3, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 1} = {0, 1, 9} by decide)) a8)

theorem c24091 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a280 a2 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 3} {1, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24093 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 9} → False := by
  intro a280 a2 a17 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 3} {1, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c24095 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {0, 3, 8} → T {0, 3, 9} → False := by
  intro a280 a2 a20 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {0, 3} {1, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c24096 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {0, 3, 8} → ¬ T {0, 3, 9} → False := by
  intro a280 n17 n20 n21
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {0, 3} {5, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) ht)
  · exact n20 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) ht)

theorem c24125 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a280 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 3} {0, 5, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24127 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a280 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 3} {0, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24135 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 5} → T {1, 5, 8} → T {1, 5, 9} → False := by
  intro a280 a4 a57 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 5} {0, 8, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c24146 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {1, 3, 9} → ¬ T {1, 5, 9} → False := by
  intro a280 n8 n49 n58
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {1, 9} {0, 3, 5} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
