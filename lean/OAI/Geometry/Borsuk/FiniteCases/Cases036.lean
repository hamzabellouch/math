import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c9739 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a177 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 6} {1, 7, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c9741 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {2, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a177 a72 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 6} {2, 7, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c9742 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 4, 7} → ¬ T {2, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a177 n52 n73 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {4, 7} {1, 2, 6} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c9745 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a177 a52 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 7} {1, 2, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c9746 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a177 n52 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 5, 8} {4, 7} {1, 6, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c9755 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a177 a54 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {4, 9} {1, 6, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c9763 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  intro a177 a59 a105 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 7} {1, 4, 9} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c9773 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {2, 6, 9} → T {4, 6, 9} → T {6, 7, 9} → False := by
  intro a177 a82 a107 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {6, 9} {2, 4, 7} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {6, 9} = {2, 6, 9} by decide)) a82)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c9779 (h : TenSystem T Q) :
    Q {0, 3, 5, 8} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a177 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 8} {7, 9} {1, 4, 6} a177 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c9782 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 4} → ¬ T {6, 7, 8} → False := by
  intro a178 n38 n117
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 4} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n117)

theorem c9784 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 6} → ¬ T {4, 7, 8} → False := by
  intro a178 n40 n108
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 6} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n40 (hc.mpr n108)

theorem c9788 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → ¬ T {1, 2, 8} → ¬ T {4, 6, 7} → False := by
  intro a178 n42 n105
  have hc := h.complementary {0, 3, 5, 9} {1, 2, 8} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n105)

theorem c9793 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → T {1, 4, 7} → T {2, 6, 8} → False := by
  intro a178 a52 a81
  have hc := h.complementary {0, 3, 5, 9} {1, 4, 7} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a81

theorem c9801 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → T {1, 7, 8} → T {2, 4, 6} → False := by
  intro a178 a62 a72
  have hc := h.complementary {0, 3, 5, 9} {1, 7, 8} a178 (by decide) (by decide)
  have he : ( {0, 3, 5, 9} : Finset Labels)ᶜ \ {1, 7, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a62 a72

theorem c9875 (h : TenSystem T Q) :
    Q {0, 3, 5, 9} → T {1, 4, 6} → T {2, 4, 6} → T {4, 6, 7} → False := by
  intro a178 a51 a72 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 5, 9} {4, 6} {1, 2, 7} a178 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c9922 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 2, 4} → ¬ T {5, 8, 9} → False := by
  intro a179 n38 n116
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 4} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n116)

theorem c9923 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 2, 4} → T {5, 8, 9} → False := by
  intro a179 a38 a116
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 4} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a116

theorem c9924 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 2, 5} → ¬ T {4, 8, 9} → False := by
  intro a179 n39 n110
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 5} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 8, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n110)

theorem c9928 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 2, 9} → ¬ T {4, 5, 8} → False := by
  intro a179 n43 n103
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 9} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n43 (hc.mpr n103)

theorem c9929 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 2, 9} → T {4, 5, 8} → False := by
  intro a179 a43 a103
  have hc := h.complementary {0, 3, 6, 7} {1, 2, 9} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 2, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a43 a103

theorem c9937 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 5, 8} → T {2, 4, 9} → False := by
  intro a179 a57 a75
  have hc := h.complementary {0, 3, 6, 7} {1, 5, 8} a179 (by decide) (by decide)
  have he : ( {0, 3, 6, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a75

theorem c9979 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 2, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a179 a43 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 7} {1, 9} {2, 5, 8} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c10011 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 2, 9} → T {2, 5, 9} → T {2, 8, 9} → False := by
  intro a179 a43 a79 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 7} {2, 9} {1, 5, 8} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c10020 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a179 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 7} {4, 5} {2, 8, 9} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c10035 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a179 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 7} {4, 9} {1, 5, 8} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c10039 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → T {1, 5, 8} → T {2, 5, 8} → T {4, 5, 8} → False := by
  intro a179 a57 a78 a103
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 7} {5, 8} {1, 2, 4} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)

theorem c10042 (h : TenSystem T Q) :
    Q {0, 3, 6, 7} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a179 n57 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 7} {5, 8} {1, 4, 9} a179 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c10062 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {1, 2, 4} → ¬ T {5, 7, 9} → False := by
  intro a180 n38 n115
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 4} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n115)

theorem c10064 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {1, 2, 5} → ¬ T {4, 7, 9} → False := by
  intro a180 n39 n109
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 5} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n109)

theorem c10067 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 2, 7} → T {4, 5, 9} → False := by
  intro a180 a41 a104
  have hc := h.complementary {0, 3, 6, 8} {1, 2, 7} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a41 a104

theorem c10081 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 7, 9} → T {2, 4, 5} → False := by
  intro a180 a63 a71
  have hc := h.complementary {0, 3, 6, 8} {1, 7, 9} a180 (by decide) (by decide)
  have he : ( {0, 3, 6, 8} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a63 a71

theorem c10155 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a180 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 8} {4, 5} {1, 2, 7} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10165 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → T {1, 4, 7} → T {2, 4, 7} → T {4, 7, 9} → False := by
  intro a180 a52 a73 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 8} {4, 7} {1, 2, 9} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c10184 (h : TenSystem T Q) :
    Q {0, 3, 6, 8} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a180 n77 n102 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 8} {5, 7} {2, 4, 9} a180 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c10202 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 4} → ¬ T {5, 7, 8} → False := by
  intro a181 n38 n114
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 4} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n114)

theorem c10203 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 2, 4} → T {5, 7, 8} → False := by
  intro a181 a38 a114
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 4} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a38 a114

theorem c10204 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 5} → ¬ T {4, 7, 8} → False := by
  intro a181 n39 n108
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 5} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n108)

theorem c10206 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a181 n41 n103
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n41 (hc.mpr n103)

theorem c10207 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 2, 7} → T {4, 5, 8} → False := by
  intro a181 a41 a103
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a41 a103

theorem c10208 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 2, 8} → ¬ T {4, 5, 7} → False := by
  intro a181 n42 n102
  have hc := h.complementary {0, 3, 6, 9} {1, 2, 8} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n102)

theorem c10213 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 4, 7} → T {2, 5, 8} → False := by
  intro a181 a52 a78
  have hc := h.complementary {0, 3, 6, 9} {1, 4, 7} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a78

theorem c10219 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 5, 8} → T {2, 4, 7} → False := by
  intro a181 a57 a73
  have hc := h.complementary {0, 3, 6, 9} {1, 5, 8} a181 (by decide) (by decide)
  have he : ( {0, 3, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a73

theorem c10295 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → T {1, 4, 5} → T {2, 4, 5} → T {4, 5, 7} → False := by
  intro a181 a50 a71 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 3, 6, 9} {4, 5} {1, 2, 7} a181 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c10330 (h : TenSystem T Q) :
    Q {0, 3, 6, 9} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a181 n57 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 3, 6, 9} {5, 8} {1, 4, 7} a181 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c10343 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 4} → T {5, 6, 9} → False := by
  intro a182 a38 a113
  have hc := h.complementary {0, 3, 7, 8} {1, 2, 4} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 2, 4} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a38 a113

theorem c10344 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → ¬ T {1, 2, 5} → ¬ T {4, 6, 9} → False := by
  intro a182 n39 n107
  have hc := h.complementary {0, 3, 7, 8} {1, 2, 5} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 2, 5} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n107)

theorem c10347 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 2, 6} → T {4, 5, 9} → False := by
  intro a182 a40 a104
  have hc := h.complementary {0, 3, 7, 8} {1, 2, 6} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a104

theorem c10359 (h : TenSystem T Q) :
    Q {0, 3, 7, 8} → T {1, 5, 9} → T {2, 4, 6} → False := by
  intro a182 a58 a72
  have hc := h.complementary {0, 3, 7, 8} {1, 5, 9} a182 (by decide) (by decide)
  have he : ( {0, 3, 7, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a58 a72

end BorsukNine.FiniteObstruction

end OAI
