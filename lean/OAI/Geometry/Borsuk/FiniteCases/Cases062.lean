import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c22904 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → ¬ T {0, 4, 7} → ¬ T {1, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a271 n24 n52 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 8} {4, 7} {0, 1, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c22905 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → T {1, 4, 7} → T {4, 7, 9} → False := by
  intro a271 a24 a52 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {4, 7} {0, 1, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22907 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 9} → False := by
  intro a271 a24 a102 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {4, 7} {0, 5, 9} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c22939 (h : TenSystem T Q) :
    Q {2, 3, 6, 8} → T {0, 7, 9} → T {4, 7, 9} → T {5, 7, 9} → False := by
  intro a271 a35 a109 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 8} {7, 9} {0, 4, 5} a271 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)

theorem c22953 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 7} → T {1, 5, 8} → False := by
  intro a272 a24 a57
  have hc := h.complementary {2, 3, 6, 9} {0, 4, 7} a272 (by decide) (by decide)
  have he : ( {2, 3, 6, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a57

theorem c22959 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 5, 8} → T {1, 4, 7} → False := by
  intro a272 a29 a52
  have hc := h.complementary {2, 3, 6, 9} {0, 5, 8} a272 (by decide) (by decide)
  have he : ( {2, 3, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a52

theorem c22977 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 5} → T {0, 4, 7} → T {0, 4, 8} → False := by
  intro a272 a22 a24 a25
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {0, 4} {5, 7, 8} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 4} = {0, 4, 8} by decide)) a25)

theorem c22978 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → ¬ T {0, 1, 5} → ¬ T {0, 4, 5} → ¬ T {0, 5, 7} → False := by
  intro a272 n4 n22 n28
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 6, 9} {0, 5} {1, 4, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n4 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) ht)
  · exact n22 (Eq.mp (congrArg T (show insert (4 : Labels) {0, 5} = {0, 4, 5} by decide)) ht)
  · exact n28 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 5} = {0, 5, 7} by decide)) ht)

theorem c22987 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 7} → T {0, 4, 7} → T {0, 5, 7} → False := by
  intro a272 a6 a24 a28
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {0, 7} {1, 4, 5} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 7} = {0, 1, 7} by decide)) a6)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)

theorem c23003 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 4} → T {1, 4, 5} → T {1, 4, 7} → False := by
  intro a272 a3 a50 a52
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {1, 4} {0, 5, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 4} = {0, 1, 4} by decide)) a3)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 4} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) a52)

theorem c23011 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 7} → False := by
  intro a272 a4 a50 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {1, 5} {0, 4, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c23039 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 5} → T {4, 5, 7} → T {4, 5, 8} → False := by
  intro a272 a22 a102 a103
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {4, 5} {0, 7, 8} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) a103)

theorem c23047 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 7, 8} → False := by
  intro a272 a24 a102 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {4, 7} {0, 5, 8} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c23055 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 4, 8} → T {4, 5, 8} → T {4, 7, 8} → False := by
  intro a272 a25 a103 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {4, 8} {0, 5, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c23071 (h : TenSystem T Q) :
    Q {2, 3, 6, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a272 a29 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 6, 9} {5, 8} {0, 4, 7} a272 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c23151 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a273 a4 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {1, 5} {0, 4, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c23175 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {0, 4, 5} → T {1, 4, 5} → T {4, 5, 6} → False := by
  intro a273 a22 a50 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {4, 5} {0, 1, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c23197 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → T {1, 4, 9} → T {4, 5, 9} → T {4, 6, 9} → False := by
  intro a273 a54 a104 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 8} {4, 9} {1, 5, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)

theorem c23210 (h : TenSystem T Q) :
    Q {2, 3, 7, 8} → ¬ T {0, 5, 9} → ¬ T {4, 5, 9} → ¬ T {5, 6, 9} → False := by
  intro a273 n30 n104 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 7, 8} {5, 9} {0, 4, 6} a273 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n30 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) ht)

theorem c23222 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {0, 1, 4} → ¬ T {5, 6, 8} → False := by
  intro a274 n3 n112
  have hc := h.complementary {2, 3, 7, 9} {0, 1, 4} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 1, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n3 (hc.mpr n112)

theorem c23226 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {0, 1, 6} → ¬ T {4, 5, 8} → False := by
  intro a274 n5 n103
  have hc := h.complementary {2, 3, 7, 9} {0, 1, 6} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n103)

theorem c23233 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 4, 6} → T {1, 5, 8} → False := by
  intro a274 a23 a57
  have hc := h.complementary {2, 3, 7, 9} {0, 4, 6} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a57

theorem c23239 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 5, 8} → T {1, 4, 6} → False := by
  intro a274 a29 a51
  have hc := h.complementary {2, 3, 7, 9} {0, 5, 8} a274 (by decide) (by decide)
  have he : ( {2, 3, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 4, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a51

theorem c23273 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 8} → False := by
  intro a274 a23 a27 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {0, 6} {4, 5, 8} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) a32)

theorem c23291 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 1, 5} → T {1, 4, 5} → T {1, 5, 6} → False := by
  intro a274 a4 a50 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {1, 5} {0, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c23351 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → T {0, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a274 a29 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 7, 9} {5, 8} {0, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c23352 (h : TenSystem T Q) :
    Q {2, 3, 7, 9} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a274 n57 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 7, 9} {5, 8} {1, 4, 6} a274 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c23366 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 1, 6} → ¬ T {4, 5, 7} → False := by
  intro a275 n5 n102
  have hc := h.complementary {2, 3, 8, 9} {0, 1, 6} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n102)

theorem c23368 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 1, 7} → ¬ T {4, 5, 6} → False := by
  intro a275 n6 n101
  have hc := h.complementary {2, 3, 8, 9} {0, 1, 7} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 1, 7} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n6 (hc.mpr n101)

theorem c23370 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 4, 5} → ¬ T {1, 6, 7} → False := by
  intro a275 n22 n59
  have hc := h.complementary {2, 3, 8, 9} {0, 4, 5} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {1, 6, 7} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n59)

theorem c23374 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 4, 7} → ¬ T {1, 5, 6} → False := by
  intro a275 n24 n55
  have hc := h.complementary {2, 3, 8, 9} {0, 4, 7} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {1, 5, 6} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n55)

theorem c23377 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 5, 6} → T {1, 4, 7} → False := by
  intro a275 a27 a52
  have hc := h.complementary {2, 3, 8, 9} {0, 5, 6} a275 (by decide) (by decide)
  have he : ( {2, 3, 8, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a27 a52

theorem c23413 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 7} → False := by
  intro a275 a23 a27 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {0, 6} {4, 5, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)

theorem c23445 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 4, 6} → T {1, 5, 6} → T {1, 6, 7} → False := by
  intro a275 a51 a55 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {1, 6} {4, 5, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) a59)

theorem c23461 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 4, 5} → T {4, 5, 6} → T {4, 5, 7} → False := by
  intro a275 a50 a101 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 5} {1, 6, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c23465 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 4, 6} → T {1, 4, 6} → T {4, 6, 7} → False := by
  intro a275 a23 a51 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 6} {0, 1, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c23466 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → False := by
  intro a275 n23 n101 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 8, 9} {4, 6} {0, 5, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c23469 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 7} → False := by
  intro a275 a51 a101 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 6} {1, 5, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c23475 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 4, 7} → T {4, 5, 7} → T {4, 6, 7} → False := by
  intro a275 a24 a102 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {4, 7} {0, 5, 6} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)

theorem c23483 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {0, 5, 6} → T {4, 5, 6} → T {5, 6, 7} → False := by
  intro a275 a27 a101 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {5, 6} {0, 4, 7} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c23493 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → T {1, 5, 7} → T {4, 5, 7} → T {5, 6, 7} → False := by
  intro a275 a56 a102 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 3, 8, 9} {5, 7} {1, 4, 6} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)

theorem c23496 (h : TenSystem T Q) :
    Q {2, 3, 8, 9} → ¬ T {0, 6, 7} → ¬ T {1, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a275 n31 n59 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 3, 8, 9} {6, 7} {0, 1, 5} a275 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n31 (Eq.mp (congrArg T (show insert (0 : Labels) {6, 7} = {0, 6, 7} by decide)) ht)
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

theorem c23503 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 1, 3} → T {7, 8, 9} → False := by
  intro a276 a2 a120
  have hc := h.complementary {2, 4, 5, 6} {0, 1, 3} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 1, 3} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a2 a120

theorem c23512 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → ¬ T {0, 3, 8} → ¬ T {1, 7, 9} → False := by
  intro a276 n20 n63
  have hc := h.complementary {2, 4, 5, 6} {0, 3, 8} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 8} = {1, 7, 9} := by decide
  rw [he] at hc
  exact n20 (hc.mpr n63)

theorem c23515 (h : TenSystem T Q) :
    Q {2, 4, 5, 6} → T {0, 3, 9} → T {1, 7, 8} → False := by
  intro a276 a21 a62
  have hc := h.complementary {2, 4, 5, 6} {0, 3, 9} a276 (by decide) (by decide)
  have he : ( {2, 4, 5, 6} : Finset Labels)ᶜ \ {0, 3, 9} = {1, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a21 a62

end BorsukNine.FiniteObstruction

end OAI
