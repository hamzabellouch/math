import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c22528 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 8} → ¬ T {4, 6, 7} → False := by
  intro a269 n7 n105
  have hc := h.complementary {2, 3, 5, 9} {0, 1, 8} a269 (by decide) (by decide)
  have he : ( {2, 3, 5, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n105)

theorem c22542 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 1, 4} → ¬ T {0, 1, 6} → ¬ T {0, 1, 7} → False := by
  intro a269 n3 n5 n6
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 9} {0, 1} {4, 6, 7} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 1} = {0, 1, 4} by decide)) ht)
  · exact n5 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) ht)
  · exact n6 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) ht)

theorem c22565 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {0, 4, 6} → T {0, 6, 7} → T {0, 6, 8} → False := by
  intro a269 a23 a31 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {0, 6} {4, 7, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) a32)

theorem c22597 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {1, 4, 6} → T {1, 6, 7} → T {1, 6, 8} → False := by
  intro a269 a51 a59 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {1, 6} {4, 7, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 6} = {1, 6, 8} by decide)) a60)

theorem c22615 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a269 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {4, 6} {0, 1, 7} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c22618 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 8} → False := by
  intro a269 n23 n105 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 9} {4, 6} {0, 7, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)

theorem c22621 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 8} → False := by
  intro a269 a51 a105 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {4, 6} {1, 7, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c22627 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 8} → False := by
  intro a269 a24 a105 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {4, 7} {0, 6, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c22640 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 6, 7} → ¬ T {1, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a269 n31 n59 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 9} {6, 7} {0, 1, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c22642 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → ¬ T {0, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a269 n31 n105 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 5, 9} {6, 7} {0, 4, 8} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c22651 (h : TenSystem T Q) :
    Q {2, 3, 5, 9} → T {0, 6, 8} → T {4, 6, 8} → T {6, 7, 8} → False := by
  intro a269 a32 a106 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 5, 9} {6, 8} {0, 4, 7} a269 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c22663 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {5, 8, 9} → False := by
  intro a270 a3 a116
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 4} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a3 a116

theorem c22664 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 5} → ¬ T {4, 8, 9} → False := by
  intro a270 n4 n110
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n110)

theorem c22665 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 5} → T {4, 8, 9} → False := by
  intro a270 a4 a110
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a4 a110

theorem c22668 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 9} → ¬ T {4, 5, 8} → False := by
  intro a270 n8 n103
  have hc := h.complementary {2, 3, 6, 7} {0, 1, 9} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 1, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n8 (hc.mpr n103)

theorem c22670 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 4, 5} → ¬ T {1, 8, 9} → False := by
  intro a270 n22 n64
  have hc := h.complementary {2, 3, 6, 7} {0, 4, 5} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 8, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n64)

theorem c22674 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 4, 9} → ¬ T {1, 5, 8} → False := by
  intro a270 n26 n57
  have hc := h.complementary {2, 3, 6, 7} {0, 4, 9} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 4, 9} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n26 (hc.mpr n57)

theorem c22677 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 5, 8} → T {1, 4, 9} → False := by
  intro a270 a29 a54
  have hc := h.complementary {2, 3, 6, 7} {0, 5, 8} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a29 a54

theorem c22679 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 5, 9} → T {1, 4, 8} → False := by
  intro a270 a30 a53
  have hc := h.complementary {2, 3, 6, 7} {0, 5, 9} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a30 a53

theorem c22681 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 8, 9} → T {1, 4, 5} → False := by
  intro a270 a36 a50
  have hc := h.complementary {2, 3, 6, 7} {0, 8, 9} a270 (by decide) (by decide)
  have he : ( {2, 3, 6, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {1, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a36 a50

theorem c22690 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 4} → ¬ T {0, 4, 5} → ¬ T {0, 4, 8} → False := by
  intro a270 n3 n22 n25
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {0, 4} {1, 5, 8} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) ht)
  · exact n25 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 4} = {0, 4, 8} by decide)) ht)

theorem c22723 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 8} → False := by
  intro a270 a3 a50 a53
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {1, 4} {0, 5, 8} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 4} = {1, 4, 8} by decide)) a53)

theorem c22724 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 4} → ¬ T {1, 4, 5} → ¬ T {1, 4, 9} → False := by
  intro a270 n3 n50 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {1, 4} {0, 5, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) ht)
  · exact n50 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) ht)

theorem c22725 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 9} → False := by
  intro a270 a3 a50 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {1, 4} {0, 5, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c22726 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 1, 4} → ¬ T {1, 4, 8} → ¬ T {1, 4, 9} → False := by
  intro a270 n3 n53 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {1, 4} {0, 8, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n3 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) ht)
  · exact n53 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 4} = {1, 4, 8} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) ht)

theorem c22766 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 4, 8} → ¬ T {4, 5, 8} → ¬ T {4, 8, 9} → False := by
  intro a270 n25 n103 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {4, 8} {0, 5, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c22777 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a270 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {4, 9} {1, 5, 8} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c22780 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a270 n29 n57 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {5, 8} {0, 1, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c22781 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 5, 8} → T {1, 5, 8} → T {5, 8, 9} → False := by
  intro a270 a29 a57 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {5, 8} {0, 1, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c22783 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a270 a29 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {5, 8} {0, 4, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c22784 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a270 n57 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 7} {5, 8} {1, 4, 9} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c22799 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {0, 8, 9} → T {4, 8, 9} → T {5, 8, 9} → False := by
  intro a270 a36 a110 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {8, 9} {0, 4, 5} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c22801 (h : TenSystem T Q) :
    Q {2, 3, 6, 7} → T {1, 8, 9} → T {4, 8, 9} → T {5, 8, 9} → False := by
  intro a270 a64 a110 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 7} {8, 9} {1, 4, 5} a270 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c22802 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 4} → ¬ T {5, 7, 9} → False := by
  intro a271 n3 n115
  have hc := h.complementary {2, 3, 6, 8} {0, 1, 4} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n115)

theorem c22804 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 5} → ¬ T {4, 7, 9} → False := by
  intro a271 n4 n109
  have hc := h.complementary {2, 3, 6, 8} {0, 1, 5} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n109)

theorem c22805 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 5} → T {4, 7, 9} → False := by
  intro a271 a4 a109
  have hc := h.complementary {2, 3, 6, 8} {0, 1, 5} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a4 a109

theorem c22811 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 5} → T {1, 7, 9} → False := by
  intro a271 a22 a63
  have hc := h.complementary {2, 3, 6, 8} {0, 4, 5} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a63

theorem c22813 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → T {1, 5, 9} → False := by
  intro a271 a24 a58
  have hc := h.complementary {2, 3, 6, 8} {0, 4, 7} a271 (by decide) (by decide)
  have he : ( {2, 3, 6, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a58

theorem c22831 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 4} → T {0, 4, 5} → T {0, 4, 7} → False := by
  intro a271 a3 a22 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {0, 4} {1, 5, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c22838 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a271 n4 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 8} {0, 5} {1, 4, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c22840 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 1, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 9} → False := by
  intro a271 n4 n22 n30
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 8} {0, 5} {1, 4, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n30 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 5} = {0, 5, 9} by decide)) ht)

theorem c22847 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 7} → T {0, 4, 7} → T {0, 5, 7} → False := by
  intro a271 a6 a24 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {0, 7} {1, 4, 5} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) a6)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)

theorem c22861 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 9} → T {0, 5, 9} → T {0, 7, 9} → False := by
  intro a271 a26 a30 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {0, 9} {4, 5, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c22863 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 7} → False := by
  intro a271 a3 a50 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {1, 4} {0, 5, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c22871 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a271 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {1, 5} {0, 4, 7} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

end BorsukNine.FiniteObstruction

end OAI
