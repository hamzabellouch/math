import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c18039 (h : TenSystem T Q) :
    Q {1, 3, 6, 8} → T {0, 7, 9} → T {4, 7, 9} → T {5, 7, 9} → False := by
  intro a236 a35 a109 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 8} {7, 9} {0, 4, 5} a236 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)

theorem c18042 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 4} → ¬ T {5, 7, 8} → False := by
  intro a237 n10 n114
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 4} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n114)

theorem c18043 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 4} → T {5, 7, 8} → False := by
  intro a237 a10 a114
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 4} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a114

theorem c18044 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 5} → ¬ T {4, 7, 8} → False := by
  intro a237 n11 n108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n108)

theorem c18045 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 5} → T {4, 7, 8} → False := by
  intro a237 a11 a108
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 5} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a108

theorem c18046 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 2, 7} → ¬ T {4, 5, 8} → False := by
  intro a237 n13 n103
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n103)

theorem c18047 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 2, 7} → T {4, 5, 8} → False := by
  intro a237 a13 a103
  have hc := h.complementary {1, 3, 6, 9} {0, 2, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a13 a103

theorem c18054 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 4, 8} → ¬ T {2, 5, 7} → False := by
  intro a237 n25 n77
  have hc := h.complementary {1, 3, 6, 9} {0, 4, 8} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 5, 7} := by decide
  rw [he] at hc
  exact n25 (hc.mpr n77)

theorem c18055 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 4, 8} → T {2, 5, 7} → False := by
  intro a237 a25 a77
  have hc := h.complementary {1, 3, 6, 9} {0, 4, 8} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 4, 8} = {2, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a25 a77

theorem c18056 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 5, 7} → ¬ T {2, 4, 8} → False := by
  intro a237 n28 n74
  have hc := h.complementary {1, 3, 6, 9} {0, 5, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n74)

theorem c18057 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 5, 7} → T {2, 4, 8} → False := by
  intro a237 a28 a74
  have hc := h.complementary {1, 3, 6, 9} {0, 5, 7} a237 (by decide) (by decide)
  have he : ( {1, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a28 a74

theorem c18153 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → T {0, 4, 8} → T {2, 4, 8} → T {4, 7, 8} → False := by
  intro a237 a25 a74 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 6, 9} {4, 8} {0, 2, 7} a237 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c18158 (h : TenSystem T Q) :
    Q {1, 3, 6, 9} → ¬ T {0, 5, 7} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → False := by
  intro a237 n28 n77 n102
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 6, 9} {5, 7} {0, 2, 4} a237 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)

theorem c18182 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 4} → ¬ T {5, 6, 9} → False := by
  intro a238 n10 n113
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 4} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n113)

theorem c18184 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 5} → ¬ T {4, 6, 9} → False := by
  intro a238 n11 n107
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 5} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n107)

theorem c18186 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 6} → ¬ T {4, 5, 9} → False := by
  intro a238 n12 n104
  have hc := h.complementary {1, 3, 7, 8} {0, 2, 6} a238 (by decide) (by decide)
  have he : ( {1, 3, 7, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n104)

theorem c18237 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → T {0, 2, 9} → T {0, 4, 9} → T {0, 6, 9} → False := by
  intro a238 a15 a26 a33
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 8} {0, 9} {2, 4, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)

theorem c18268 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → ¬ T {0, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 6, 9} → False := by
  intro a238 n15 n75 n82
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 8} {2, 9} {0, 4, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n15 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 9} = {0, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n82 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 9} = {2, 6, 9} by decide)) ht)

theorem c18275 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → T {0, 4, 5} → T {2, 4, 5} → T {4, 5, 6} → False := by
  intro a238 a22 a71 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 8} {4, 5} {0, 2, 6} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c18285 (h : TenSystem T Q) :
    Q {1, 3, 7, 8} → T {0, 4, 6} → T {2, 4, 6} → T {4, 6, 9} → False := by
  intro a238 a23 a72 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 8} {4, 6} {0, 2, 9} a238 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c18322 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 8} → False := by
  intro a239 n10 n112
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 4} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n112)

theorem c18323 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 4} → T {5, 6, 8} → False := by
  intro a239 a10 a112
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 4} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a10 a112

theorem c18324 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 8} → False := by
  intro a239 n11 n106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n106)

theorem c18325 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 5} → T {4, 6, 8} → False := by
  intro a239 a11 a106
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 5} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a106

theorem c18326 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 6} → ¬ T {4, 5, 8} → False := by
  intro a239 n12 n103
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n103)

theorem c18327 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 6} → T {4, 5, 8} → False := by
  intro a239 a12 a103
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a103

theorem c18328 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 2, 8} → ¬ T {4, 5, 6} → False := by
  intro a239 n14 n101
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 8} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n101)

theorem c18329 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 2, 8} → T {4, 5, 6} → False := by
  intro a239 a14 a101
  have hc := h.complementary {1, 3, 7, 9} {0, 2, 8} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a101

theorem c18336 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 4, 8} → False := by
  intro a239 n27 n74
  have hc := h.complementary {1, 3, 7, 9} {0, 5, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 8} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n74)

theorem c18337 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 5, 6} → T {2, 4, 8} → False := by
  intro a239 a27 a74
  have hc := h.complementary {1, 3, 7, 9} {0, 5, 6} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 4, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a74

theorem c18339 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 5, 8} → T {2, 4, 6} → False := by
  intro a239 a29 a72
  have hc := h.complementary {1, 3, 7, 9} {0, 5, 8} a239 (by decide) (by decide)
  have he : ( {1, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a72

theorem c18397 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {2, 4, 5} → T {2, 5, 6} → T {2, 5, 8} → False := by
  intro a239 a71 a76 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {2, 5} {4, 6, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 5} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 5} = {2, 5, 8} by decide)) a78)

theorem c18405 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {2, 4, 6} → T {2, 5, 6} → T {2, 6, 8} → False := by
  intro a239 a72 a76 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {2, 6} {4, 5, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) a76)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) a81)

theorem c18427 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → T {0, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a239 a23 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 3, 7, 9} {4, 6} {0, 5, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c18430 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 4, 8} → ¬ T {2, 4, 8} → ¬ T {4, 5, 8} → False := by
  intro a239 n25 n74 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {4, 8} {0, 2, 5} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n74 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 8} = {2, 4, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)

theorem c18438 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {4, 5, 6} → False := by
  intro a239 n27 n76 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 6} {0, 2, 4} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)

theorem c18440 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 6} → ¬ T {2, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a239 n27 n76 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 6} {0, 2, 8} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 6} = {2, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c18450 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {0, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a239 n29 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 8} {0, 4, 6} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c18452 (h : TenSystem T Q) :
    Q {1, 3, 7, 9} → ¬ T {2, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a239 n78 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 3, 7, 9} {5, 8} {2, 4, 6} a239 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c18462 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 4} → ¬ T {5, 6, 7} → False := by
  intro a240 n10 n111
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 4} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n10 (hc.mpr n111)

theorem c18463 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 4} → T {5, 6, 7} → False := by
  intro a240 a10 a111
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 4} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 4} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a10 a111

theorem c18464 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 5} → ¬ T {4, 6, 7} → False := by
  intro a240 n11 n105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n105)

theorem c18465 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 5} → T {4, 6, 7} → False := by
  intro a240 a11 a105
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a11 a105

theorem c18466 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 6} → ¬ T {4, 5, 7} → False := by
  intro a240 n12 n102
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n102)

theorem c18467 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 6} → T {4, 5, 7} → False := by
  intro a240 a12 a102
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 6} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a12 a102

theorem c18468 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 2, 7} → ¬ T {4, 5, 6} → False := by
  intro a240 n13 n101
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n101)

theorem c18469 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 2, 7} → T {4, 5, 6} → False := by
  intro a240 a13 a101
  have hc := h.complementary {1, 3, 8, 9} {0, 2, 7} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a13 a101

theorem c18470 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {2, 6, 7} → False := by
  intro a240 n22 n80
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n80)

theorem c18471 (h : TenSystem T Q) :
    Q {1, 3, 8, 9} → T {0, 4, 5} → T {2, 6, 7} → False := by
  intro a240 a22 a80
  have hc := h.complementary {1, 3, 8, 9} {0, 4, 5} a240 (by decide) (by decide)
  have he : ( {1, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {2, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a22 a80

end BorsukNine.FiniteObstruction

end OAI
