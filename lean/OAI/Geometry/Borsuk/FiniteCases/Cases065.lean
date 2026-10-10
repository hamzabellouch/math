import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c24639 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → T {1, 3, 6} → False := by
  intro a284 a29 a46
  have hc := h.complementary {2, 4, 7, 9} {0, 5, 8} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a46

theorem c24643 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 6} → False := by
  intro a284 a2 a4 a5
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 1} {3, 5, 6} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)

theorem c24647 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 1, 6} → T {0, 1, 8} → False := by
  intro a284 a2 a5 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 1} {3, 6, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c24653 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a284 a2 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {0, 3} {1, 5, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24703 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 6} → T {1, 5, 6} → T {1, 6, 8} → False := by
  intro a284 a5 a55 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {1, 6} {0, 5, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 6} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) a60)

theorem c24724 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {1, 3, 6} → ¬ T {3, 6, 8} → False := by
  intro a284 n18 n46 n96
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {3, 6} {0, 1, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n18 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 6} = {0, 3, 6} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) ht)

theorem c24742 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a284 n27 n91 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {5, 6} {0, 3, 8} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c24747 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 5, 8} → T {1, 5, 8} → T {3, 5, 8} → False := by
  intro a284 a29 a57 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 9} {5, 8} {0, 1, 3} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c24748 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a284 n29 n57 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {5, 8} {0, 1, 6} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c24750 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a284 n29 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 9} {5, 8} {0, 3, 6} a284 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c24785 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a285 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {0, 1} {3, 5, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c24803 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 5} → T {0, 5, 6} → T {0, 5, 7} → False := by
  intro a285 a4 a27 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {0, 5} {1, 6, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 5} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) a28)

theorem c24827 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a285 a2 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {1, 3} {0, 6, 7} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c24895 (h : TenSystem T Q) :
    Q {2, 4, 8, 9} → T {0, 6, 7} → T {1, 6, 7} → T {3, 6, 7} → False := by
  intro a285 a31 a59 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 8, 9} {6, 7} {0, 1, 3} a285 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)

theorem c24903 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → T {0, 1, 3} → T {4, 8, 9} → False := by
  intro a286 a2 a110
  have hc := h.complementary {2, 5, 6, 7} {0, 1, 3} a286 (by decide) (by decide)
  have he : ( {2, 5, 6, 7} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a110

theorem c24916 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → ¬ T {0, 4, 8} → ¬ T {1, 3, 9} → False := by
  intro a286 n25 n49
  have hc := h.complementary {2, 5, 6, 7} {0, 4, 8} a286 (by decide) (by decide)
  have he : ( {2, 5, 6, 7} : Finset Labels)ᶜ \ {0, 4, 8} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n49)

theorem c24965 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a286 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 7} {1, 3} {0, 4, 9} a286 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24967 (h : TenSystem T Q) :
    Q {2, 5, 6, 7} → T {0, 1, 3} → T {1, 3, 8} → T {1, 3, 9} → False := by
  intro a286 a2 a48 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 7} {1, 3} {0, 8, 9} a286 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c25043 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {4, 7, 9} → False := by
  intro a287 a2 a109
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 3} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a109

theorem c25045 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 4} → T {3, 7, 9} → False := by
  intro a287 a3 a99
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 4} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a99

theorem c25048 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 1, 9} → ¬ T {3, 4, 7} → False := by
  intro a287 n8 n88
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 9} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n88)

theorem c25049 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 9} → T {3, 4, 7} → False := by
  intro a287 a8 a88
  have hc := h.complementary {2, 5, 6, 8} {0, 1, 9} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a8 a88

theorem c25056 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 3, 9} → False := by
  intro a287 n24 n49
  have hc := h.complementary {2, 5, 6, 8} {0, 4, 7} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n49)

theorem c25057 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 4, 7} → T {1, 3, 9} → False := by
  intro a287 a24 a49
  have hc := h.complementary {2, 5, 6, 8} {0, 4, 7} a287 (by decide) (by decide)
  have he : ( {2, 5, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a49

theorem c25073 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {0, 3, 4} → T {0, 3, 9} → False := by
  intro a287 a2 a16 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {0, 3} {1, 4, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c25075 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 9} → False := by
  intro a287 a2 a19 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {0, 3} {1, 7, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c25097 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a287 a8 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {0, 9} {1, 3, 7} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c25107 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a287 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {1, 3} {0, 7, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c25126 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 1, 9} → ¬ T {1, 3, 9} → ¬ T {1, 4, 9} → False := by
  intro a287 n8 n49 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 6, 8} {1, 9} {0, 3, 4} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) ht)

theorem c25131 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 1, 9} → T {1, 4, 9} → T {1, 7, 9} → False := by
  intro a287 a8 a54 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {1, 9} {0, 4, 7} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) a63)

theorem c25150 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a287 n21 n49 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 6, 8} {3, 9} {0, 1, 4} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c25159 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → T {0, 4, 7} → T {1, 4, 7} → T {3, 4, 7} → False := by
  intro a287 a24 a52 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 8} {4, 7} {0, 1, 3} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c25162 (h : TenSystem T Q) :
    Q {2, 5, 6, 8} → ¬ T {0, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a287 n24 n88 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 6, 8} {4, 7} {0, 3, 9} a287 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c25183 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → T {0, 1, 3} → T {4, 7, 8} → False := by
  intro a288 a2 a108
  have hc := h.complementary {2, 5, 6, 9} {0, 1, 3} a288 (by decide) (by decide)
  have he : ( {2, 5, 6, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a108

theorem c25188 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → ¬ T {0, 1, 8} → ¬ T {3, 4, 7} → False := by
  intro a288 n7 n88
  have hc := h.complementary {2, 5, 6, 9} {0, 1, 8} a288 (by decide) (by decide)
  have he : ( {2, 5, 6, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n88)

theorem c25196 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → ¬ T {0, 4, 7} → ¬ T {1, 3, 8} → False := by
  intro a288 n24 n48
  have hc := h.complementary {2, 5, 6, 9} {0, 4, 7} a288 (by decide) (by decide)
  have he : ( {2, 5, 6, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 3, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n48)

theorem c25215 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a288 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 9} {0, 3} {1, 7, 8} a288 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c25243 (h : TenSystem T Q) :
    Q {2, 5, 6, 9} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a288 a2 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 6, 9} {1, 3} {0, 4, 7} a288 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c25329 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 9} → T {3, 4, 6} → False := by
  intro a289 a8 a87
  have hc := h.complementary {2, 5, 7, 8} {0, 1, 9} a289 (by decide) (by decide)
  have he : ( {2, 5, 7, 8} : Finset Labels)ᶜ \ {0, 1, 9} = {3, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a8 a87

theorem c25334 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 3, 9} → ¬ T {1, 4, 6} → False := by
  intro a289 n21 n51
  have hc := h.complementary {2, 5, 7, 8} {0, 3, 9} a289 (by decide) (by decide)
  have he : ( {2, 5, 7, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact n21 (hc.mpr n51)

theorem c25335 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 3, 9} → T {1, 4, 6} → False := by
  intro a289 a21 a51
  have hc := h.complementary {2, 5, 7, 8} {0, 3, 9} a289 (by decide) (by decide)
  have he : ( {2, 5, 7, 8} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a21 a51

theorem c25336 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 4, 6} → ¬ T {1, 3, 9} → False := by
  intro a289 n23 n49
  have hc := h.complementary {2, 5, 7, 8} {0, 4, 6} a289 (by decide) (by decide)
  have he : ( {2, 5, 7, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n49)

theorem c25351 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 4} → T {0, 3, 6} → False := by
  intro a289 a2 a16 a18
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 4, 6} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 3} = {0, 3, 4} by decide)) a16)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)

theorem c25355 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a289 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {0, 3} {1, 6, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c25368 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → ¬ T {0, 1, 6} → ¬ T {0, 3, 6} → ¬ T {0, 6, 9} → False := by
  intro a289 n5 n18 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 5, 7, 8} {0, 6} {1, 3, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n18 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c25385 (h : TenSystem T Q) :
    Q {2, 5, 7, 8} → T {0, 1, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a289 a2 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 5, 7, 8} {1, 3} {0, 4, 9} a289 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

end BorsukNine.FiniteObstruction

end OAI
