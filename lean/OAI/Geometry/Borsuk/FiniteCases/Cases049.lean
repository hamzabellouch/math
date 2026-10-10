import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c16605 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 8} → T {2, 6, 8} → T {6, 8, 9} → False := by
  intro a226 a32 a81 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 8} {0, 2, 9} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) a81)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c16607 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a226 a32 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 8} {0, 7, 9} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c16611 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 6, 9} → T {2, 6, 9} → T {6, 7, 9} → False := by
  intro a226 a33 a82 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {6, 9} {0, 2, 7} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c16639 (h : TenSystem T Q) :
    Q {1, 3, 4, 5} → T {0, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a226 a36 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 5} {8, 9} {0, 6, 7} a226 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c16645 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 2, 7} → T {5, 8, 9} → False := by
  intro a227 a13 a116
  have hc := h.complementary {1, 3, 4, 6} {0, 2, 7} a227 (by decide) (by decide)
  have he : ( {1, 3, 4, 6} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a13 a116

theorem c16649 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 2, 9} → T {5, 7, 8} → False := by
  intro a227 a15 a114
  have hc := h.complementary {1, 3, 4, 6} {0, 2, 9} a227 (by decide) (by decide)
  have he : ( {1, 3, 4, 6} : Finset Labels)ᶜ \ {0, 2, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a114

theorem c16651 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 5, 7} → T {2, 8, 9} → False := by
  intro a227 a28 a85
  have hc := h.complementary {1, 3, 4, 6} {0, 5, 7} a227 (by decide) (by decide)
  have he : ( {1, 3, 4, 6} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a85

theorem c16745 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a227 a29 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {5, 8} {0, 2, 9} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c16746 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → ¬ T {0, 5, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a227 n29 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 6} {5, 8} {0, 7, 9} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c16749 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {2, 5, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a227 a78 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {5, 8} {2, 7, 9} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c16755 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 5, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a227 a30 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {5, 9} {0, 7, 8} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c16779 (h : TenSystem T Q) :
    Q {1, 3, 4, 6} → T {0, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a227 a36 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 6} {8, 9} {0, 5, 7} a227 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c16782 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 5} → ¬ T {6, 8, 9} → False := by
  intro a228 n11 n119
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 5} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n119)

theorem c16784 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 6} → ¬ T {5, 8, 9} → False := by
  intro a228 n12 n116
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 6} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n116)

theorem c16788 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 2, 9} → ¬ T {5, 6, 8} → False := by
  intro a228 n15 n112
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 9} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n15 (hc.mpr n112)

theorem c16789 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 2, 9} → T {5, 6, 8} → False := by
  intro a228 a15 a112
  have hc := h.complementary {1, 3, 4, 7} {0, 2, 9} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 2, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a15 a112

theorem c16797 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 6, 8} → T {2, 5, 9} → False := by
  intro a228 a32 a79
  have hc := h.complementary {1, 3, 4, 7} {0, 6, 8} a228 (by decide) (by decide)
  have he : ( {1, 3, 4, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {2, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a32 a79

theorem c16837 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 2, 9} → T {0, 5, 9} → T {0, 8, 9} → False := by
  intro a228 a15 a30 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {0, 9} {2, 5, 8} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c16883 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 5, 8} → T {2, 5, 8} → T {5, 6, 8} → False := by
  intro a228 a29 a78 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {0, 2, 6} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c16885 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 5, 8} → T {2, 5, 8} → T {5, 8, 9} → False := by
  intro a228 a29 a78 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {0, 2, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c16886 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a228 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 7} {5, 8} {0, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c16887 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a228 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {0, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c16889 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {2, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a228 a78 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {5, 8} {2, 6, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c16901 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {0, 6, 8} → T {2, 6, 8} → T {6, 8, 9} → False := by
  intro a228 a32 a81 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {6, 8} {0, 2, 9} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 8} = {0, 6, 8} by decide)) a32)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 8} = {2, 6, 8} by decide)) a81)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c16921 (h : TenSystem T Q) :
    Q {1, 3, 4, 7} → T {2, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a228 a85 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 7} {8, 9} {2, 5, 6} a228 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {8, 9} = {2, 8, 9} by decide)) a85)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c16923 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → T {0, 2, 5} → T {6, 7, 9} → False := by
  intro a229 a11 a118
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 5} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a11 a118

theorem c16924 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → ¬ T {0, 2, 6} → ¬ T {5, 7, 9} → False := by
  intro a229 n12 n115
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 6} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n115)

theorem c16926 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → ¬ T {0, 2, 7} → ¬ T {5, 6, 9} → False := by
  intro a229 n13 n113
  have hc := h.complementary {1, 3, 4, 8} {0, 2, 7} a229 (by decide) (by decide)
  have he : ( {1, 3, 4, 8} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n113)

theorem c17049 (h : TenSystem T Q) :
    Q {1, 3, 4, 8} → T {0, 6, 9} → T {2, 6, 9} → T {6, 7, 9} → False := by
  intro a229 a33 a82 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 8} {6, 9} {0, 2, 7} a229 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c17062 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {6, 7, 8} → False := by
  intro a230 n11 n117
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 5} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n117)

theorem c17063 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {6, 7, 8} → False := by
  intro a230 a11 a117
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 5} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a117

theorem c17064 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {5, 7, 8} → False := by
  intro a230 n12 n114
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 6} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n114)

theorem c17065 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 6} → T {5, 7, 8} → False := by
  intro a230 a12 a114
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 6} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a114

theorem c17066 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 7} → ¬ T {5, 6, 8} → False := by
  intro a230 n13 n112
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 7} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n112)

theorem c17067 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 7} → T {5, 6, 8} → False := by
  intro a230 a13 a112
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 7} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a112

theorem c17068 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 8} → ¬ T {5, 6, 7} → False := by
  intro a230 n14 n111
  have hc := h.complementary {1, 3, 4, 9} {0, 2, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n111)

theorem c17074 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 5, 8} → ¬ T {2, 6, 7} → False := by
  intro a230 n29 n80
  have hc := h.complementary {1, 3, 4, 9} {0, 5, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n80)

theorem c17075 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 5, 8} → T {2, 6, 7} → False := by
  intro a230 a29 a80
  have hc := h.complementary {1, 3, 4, 9} {0, 5, 8} a230 (by decide) (by decide)
  have he : ( {1, 3, 4, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a80

theorem c17082 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → False := by
  intro a230 n11 n12 n13
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {5, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)

theorem c17083 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a230 a11 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {5, 6, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c17084 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 6} → ¬ T {0, 2, 8} → False := by
  intro a230 n11 n12 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {5, 6, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c17085 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 5} → T {0, 2, 6} → T {0, 2, 8} → False := by
  intro a230 a11 a12 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {5, 6, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17088 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {0, 2, 7} → ¬ T {0, 2, 8} → False := by
  intro a230 n12 n13 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {0, 2} {6, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c17089 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → T {0, 2, 6} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a230 a12 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 4, 9} {0, 2} {6, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c17130 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {2, 5, 6} → ¬ T {2, 6, 7} → False := by
  intro a230 n12 n76 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {2, 6} {0, 5, 7} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)

theorem c17134 (h : TenSystem T Q) :
    Q {1, 3, 4, 9} → ¬ T {0, 2, 6} → ¬ T {2, 6, 7} → ¬ T {2, 6, 8} → False := by
  intro a230 n12 n80 n81
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 4, 9} {2, 6} {0, 7, 8} a230 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) ht)
  · exact n81 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
