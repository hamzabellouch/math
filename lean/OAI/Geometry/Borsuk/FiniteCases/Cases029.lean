import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c5867 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 8} → T {6, 7, 9} → False := by
  intro a150 a53 a118
  have hc := h.complementary {0, 2, 3, 5} {1, 4, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a53 a118

theorem c5872 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 6, 8} → ¬ T {4, 7, 9} → False := by
  intro a150 n60 n109
  have hc := h.complementary {0, 2, 3, 5} {1, 6, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n60 (hc.mpr n109)

theorem c5873 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 6, 8} → T {4, 7, 9} → False := by
  intro a150 a60 a109
  have hc := h.complementary {0, 2, 3, 5} {1, 6, 8} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a109

theorem c5878 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 7, 9} → ¬ T {4, 6, 8} → False := by
  intro a150 n63 n106
  have hc := h.complementary {0, 2, 3, 5} {1, 7, 9} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 7, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n106)

theorem c5881 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 8, 9} → T {4, 6, 7} → False := by
  intro a150 a64 a105
  have hc := h.complementary {0, 2, 3, 5} {1, 8, 9} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a64 a105

theorem c5924 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a150 n51 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 5} {4, 6} {1, 7, 9} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c5925 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a150 a51 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {4, 6} {1, 7, 9} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c5932 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → ¬ T {1, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a150 n52 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 5} {4, 7} {1, 6, 9} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c5933 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a150 a52 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {4, 7} {1, 6, 9} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c5987 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a150 a63 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {7, 9} {1, 4, 6} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c5995 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 8, 9} → T {4, 8, 9} → T {6, 8, 9} → False := by
  intro a150 a64 a110 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 5} {8, 9} {1, 4, 6} a150 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c6002 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 4, 5} → ¬ T {7, 8, 9} → False := by
  intro a151 n50 n120
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 5} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact n50 (hc.mpr n120)

theorem c6003 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 5} → T {7, 8, 9} → False := by
  intro a151 a50 a120
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 5} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 5} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a120

theorem c6004 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 4, 7} → ¬ T {5, 8, 9} → False := by
  intro a151 n52 n116
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 7} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n116)

theorem c6005 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 7} → T {5, 8, 9} → False := by
  intro a151 a52 a116
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 7} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a52 a116

theorem c6009 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 9} → T {5, 7, 8} → False := by
  intro a151 a54 a114
  have hc := h.complementary {0, 2, 3, 6} {1, 4, 9} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 4, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a54 a114

theorem c6012 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 5, 8} → ¬ T {4, 7, 9} → False := by
  intro a151 n57 n109
  have hc := h.complementary {0, 2, 3, 6} {1, 5, 8} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n109)

theorem c6015 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 5, 9} → T {4, 7, 8} → False := by
  intro a151 a58 a108
  have hc := h.complementary {0, 2, 3, 6} {1, 5, 9} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 5, 9} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a58 a108

theorem c6019 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 7, 9} → T {4, 5, 8} → False := by
  intro a151 a63 a103
  have hc := h.complementary {0, 2, 3, 6} {1, 7, 9} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 7, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a63 a103

theorem c6021 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 8, 9} → T {4, 5, 7} → False := by
  intro a151 a64 a102
  have hc := h.complementary {0, 2, 3, 6} {1, 8, 9} a151 (by decide) (by decide)
  have he : ( {0, 2, 3, 6} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a64 a102

theorem c6041 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → T {1, 4, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a151 a52 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 6} {1, 7} {4, 5, 9} a151 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

theorem c6130 (h : TenSystem T Q) :
    Q {0, 2, 3, 6} → ¬ T {1, 7, 9} → ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a151 n63 n115 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 6} {7, 9} {1, 5, 8} a151 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n63 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c6143 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 5} → T {6, 8, 9} → False := by
  intro a152 a50 a119
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 5} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a119

theorem c6144 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 4, 6} → ¬ T {5, 8, 9} → False := by
  intro a152 n51 n116
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n116)

theorem c6145 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 6} → T {5, 8, 9} → False := by
  intro a152 a51 a116
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a116

theorem c6149 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 9} → T {5, 6, 8} → False := by
  intro a152 a54 a112
  have hc := h.complementary {0, 2, 3, 7} {1, 4, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 4, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a54 a112

theorem c6151 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 5, 6} → T {4, 8, 9} → False := by
  intro a152 a55 a110
  have hc := h.complementary {0, 2, 3, 7} {1, 5, 6} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 5, 6} = {4, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a55 a110

theorem c6152 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 5, 8} → ¬ T {4, 6, 9} → False := by
  intro a152 n57 n107
  have hc := h.complementary {0, 2, 3, 7} {1, 5, 8} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n107)

theorem c6157 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 6, 8} → T {4, 5, 9} → False := by
  intro a152 a60 a104
  have hc := h.complementary {0, 2, 3, 7} {1, 6, 8} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 6, 8} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a60 a104

theorem c6158 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 6, 9} → ¬ T {4, 5, 8} → False := by
  intro a152 n61 n103
  have hc := h.complementary {0, 2, 3, 7} {1, 6, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n61 (hc.mpr n103)

theorem c6159 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 6, 9} → T {4, 5, 8} → False := by
  intro a152 a61 a103
  have hc := h.complementary {0, 2, 3, 7} {1, 6, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a61 a103

theorem c6161 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 8, 9} → T {4, 5, 6} → False := by
  intro a152 a64 a101
  have hc := h.complementary {0, 2, 3, 7} {1, 8, 9} a152 (by decide) (by decide)
  have he : ( {0, 2, 3, 7} : Finset Labels)ᶜ \ {1, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a64 a101

theorem c6187 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 8} → T {1, 5, 8} → T {1, 6, 8} → False := by
  intro a152 a53 a57 a60
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {1, 8} {4, 5, 6} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 8} = {1, 4, 8} by decide)) a53)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 8} = {1, 6, 8} by decide)) a60)

theorem c6201 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 5, 9} → T {1, 6, 9} → T {1, 8, 9} → False := by
  intro a152 a58 a61 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {1, 9} {5, 6, 8} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c6229 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 4, 9} → T {4, 5, 9} → T {4, 8, 9} → False := by
  intro a152 a54 a104 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {4, 9} {1, 5, 8} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c6247 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a152 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 7} {5, 8} {1, 6, 9} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c6260 (h : TenSystem T Q) :
    Q {0, 2, 3, 7} → ¬ T {1, 6, 8} → ¬ T {4, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a152 n60 n106 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 7} {6, 8} {1, 4, 9} a152 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n60 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c6283 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 5} → T {6, 7, 9} → False := by
  intro a153 a50 a118
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 5} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a50 a118

theorem c6284 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 6} → ¬ T {5, 7, 9} → False := by
  intro a153 n51 n115
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 6} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n51 (hc.mpr n115)

theorem c6285 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 6} → T {5, 7, 9} → False := by
  intro a153 a51 a115
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 6} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a115

theorem c6288 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 9} → ¬ T {5, 6, 7} → False := by
  intro a153 n54 n111
  have hc := h.complementary {0, 2, 3, 8} {1, 4, 9} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 4, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n54 (hc.mpr n111)

theorem c6292 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 5, 7} → ¬ T {4, 6, 9} → False := by
  intro a153 n56 n107
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n107)

theorem c6293 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 5, 7} → T {4, 6, 9} → False := by
  intro a153 a56 a107
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 7} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a56 a107

theorem c6294 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 5, 9} → ¬ T {4, 6, 7} → False := by
  intro a153 n58 n105
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 9} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n58 (hc.mpr n105)

theorem c6295 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 5, 9} → T {4, 6, 7} → False := by
  intro a153 a58 a105
  have hc := h.complementary {0, 2, 3, 8} {1, 5, 9} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a58 a105

theorem c6297 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 6, 7} → T {4, 5, 9} → False := by
  intro a153 a59 a104
  have hc := h.complementary {0, 2, 3, 8} {1, 6, 7} a153 (by decide) (by decide)
  have he : ( {0, 2, 3, 8} : Finset Labels)ᶜ \ {1, 6, 7} = {4, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a104

theorem c6303 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 5} → T {1, 4, 6} → T {1, 4, 7} → False := by
  intro a153 a50 a51 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {1, 4} {5, 6, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c6329 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → T {1, 4, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a153 a52 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 8} {1, 7} {4, 5, 9} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

theorem c6350 (h : TenSystem T Q) :
    Q {0, 2, 3, 8} → ¬ T {1, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a153 n51 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 8} {4, 6} {1, 5, 7} a153 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
