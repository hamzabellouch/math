import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c7879 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 3, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a164 a49 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {1, 9} {3, 5, 8} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c7910 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 3, 9} → ¬ T {3, 5, 9} → ¬ T {3, 8, 9} → False := by
  intro a164 n49 n94 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {3, 9} {1, 5, 8} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c7933 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 4, 9} → T {3, 4, 9} → T {4, 8, 9} → False := by
  intro a164 a54 a90 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {4, 9} {1, 3, 8} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c7945 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a164 a93 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {5, 8} {3, 4, 9} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c7954 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {4, 8, 9} → False := by
  intro a164 n64 n100 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {8, 9} {1, 3, 4} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)

theorem c7955 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → T {1, 8, 9} → T {3, 8, 9} → T {4, 8, 9} → False := by
  intro a164 a64 a100 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 7} {8, 9} {1, 3, 4} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)

theorem c7956 (h : TenSystem T Q) :
    Q {0, 2, 6, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a164 n64 n100 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 7} {8, 9} {1, 3, 5} a164 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c7964 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {1, 3, 5} → ¬ T {4, 7, 9} → False := by
  intro a165 n45 n109
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 5} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n109)

theorem c7968 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → ¬ T {1, 3, 9} → ¬ T {4, 5, 7} → False := by
  intro a165 n49 n102
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n102)

theorem c7969 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 3, 9} → T {4, 5, 7} → False := by
  intro a165 a49 a102
  have hc := h.complementary {0, 2, 6, 8} {1, 3, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a102

theorem c7979 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 5, 9} → T {3, 4, 7} → False := by
  intro a165 a58 a88
  have hc := h.complementary {0, 2, 6, 8} {1, 5, 9} a165 (by decide) (by decide)
  have he : ( {0, 2, 6, 8} : Finset Labels)ᶜ \ {1, 5, 9} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a58 a88

theorem c8057 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 9} → False := by
  intro a165 a50 a86 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 5} {1, 3, 9} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) a104)

theorem c8065 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 7} → T {3, 4, 7} → T {4, 7, 9} → False := by
  intro a165 a52 a88 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 7} {1, 3, 9} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c8073 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 4, 9} → T {3, 4, 9} → T {4, 7, 9} → False := by
  intro a165 a54 a90 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {4, 9} {1, 3, 7} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c8089 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 5, 9} → T {3, 5, 9} → T {5, 7, 9} → False := by
  intro a165 a58 a94 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {5, 9} {1, 3, 7} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c8095 (h : TenSystem T Q) :
    Q {0, 2, 6, 8} → T {1, 7, 9} → T {3, 7, 9} → T {4, 7, 9} → False := by
  intro a165 a63 a99 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 8} {7, 9} {1, 3, 4} a165 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)

theorem c8103 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 3, 4} → T {5, 7, 8} → False := by
  intro a166 a44 a114
  have hc := h.complementary {0, 2, 6, 9} {1, 3, 4} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 3, 4} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a44 a114

theorem c8111 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 4, 5} → T {3, 7, 8} → False := by
  intro a166 a50 a98
  have hc := h.complementary {0, 2, 6, 9} {1, 4, 5} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 4, 5} = {3, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a50 a98

theorem c8113 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 4, 7} → T {3, 5, 8} → False := by
  intro a166 a52 a93
  have hc := h.complementary {0, 2, 6, 9} {1, 4, 7} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a52 a93

theorem c8119 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 5, 8} → T {3, 4, 7} → False := by
  intro a166 a57 a88
  have hc := h.complementary {0, 2, 6, 9} {1, 5, 8} a166 (by decide) (by decide)
  have he : ( {0, 2, 6, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a57 a88

theorem c8177 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {3, 4, 5} → T {3, 5, 7} → T {3, 5, 8} → False := by
  intro a166 a86 a92 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 9} {3, 5} {4, 7, 8} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 5} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)

theorem c8205 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 4, 7} → T {3, 4, 7} → T {4, 7, 8} → False := by
  intro a166 a52 a88 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 9} {4, 7} {1, 3, 8} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c8207 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {1, 4, 7} → T {4, 5, 7} → T {4, 7, 8} → False := by
  intro a166 a52 a102 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 9} {4, 7} {1, 5, 8} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)

theorem c8228 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n57 n93 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {1, 3, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c8230 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {1, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n57 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {1, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c8232 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {5, 8} {3, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c8233 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a166 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 6, 9} {5, 8} {3, 4, 7} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c8236 (h : TenSystem T Q) :
    Q {0, 2, 6, 9} → ¬ T {1, 7, 8} → ¬ T {3, 7, 8} → ¬ T {5, 7, 8} → False := by
  intro a166 n62 n98 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 6, 9} {7, 8} {1, 3, 5} a166 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n62 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)

theorem c8248 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {1, 3, 9} → ¬ T {4, 5, 6} → False := by
  intro a167 n49 n101
  have hc := h.complementary {0, 2, 7, 8} {1, 3, 9} a167 (by decide) (by decide)
  have he : ( {0, 2, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n101)

theorem c8267 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 4} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a167 a44 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 3} {4, 6, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c8275 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 4} → T {1, 4, 6} → T {1, 4, 9} → False := by
  intro a167 a44 a51 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 4} {3, 6, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 4} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c8289 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 3, 6} → T {1, 4, 6} → T {1, 6, 9} → False := by
  intro a167 a46 a51 a61
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {1, 6} {3, 4, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 6} = {1, 6, 9} by decide)) a61)

theorem c8335 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a167 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 5} {1, 3, 6} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8342 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 5, 6} → False := by
  intro a167 n51 n87 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 8} {4, 6} {1, 3, 5} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)

theorem c8345 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 9} → False := by
  intro a167 a51 a87 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 6} {1, 3, 9} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c8351 (h : TenSystem T Q) :
    Q {0, 2, 7, 8} → T {1, 4, 9} → T {3, 4, 9} → T {4, 5, 9} → False := by
  intro a167 a54 a90 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 8} {4, 9} {1, 3, 5} a167 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 9} = {1, 4, 9} by decide)) a54)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)

theorem c8386 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 3, 6} → ¬ T {4, 5, 8} → False := by
  intro a168 n46 n103
  have hc := h.complementary {0, 2, 7, 9} {1, 3, 6} a168 (by decide) (by decide)
  have he : ( {0, 2, 7, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n46 (hc.mpr n103)

theorem c8393 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {3, 5, 8} → False := by
  intro a168 a51 a93
  have hc := h.complementary {0, 2, 7, 9} {1, 4, 6} a168 (by decide) (by decide)
  have he : ( {0, 2, 7, 9} : Finset Labels)ᶜ \ {1, 4, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a51 a93

theorem c8403 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 3, 4} → T {1, 3, 5} → T {1, 3, 6} → False := by
  intro a168 a44 a45 a46
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {1, 3} {4, 5, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)

theorem c8475 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a168 a50 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 5} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 5} = {1, 4, 5} by decide)) a50)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c8482 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 5, 6} → False := by
  intro a168 n51 n87 n101
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {4, 6} {1, 3, 5} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)

theorem c8485 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {3, 4, 6} → T {4, 6, 8} → False := by
  intro a168 a51 a87 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 6} {1, 3, 8} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c8487 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 4, 6} → T {4, 5, 6} → T {4, 6, 8} → False := by
  intro a168 a51 a101 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {4, 6} {1, 5, 8} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c8508 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a168 n57 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 7, 9} {5, 8} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c8509 (h : TenSystem T Q) :
    Q {0, 2, 7, 9} → T {1, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a168 a57 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 7, 9} {5, 8} {1, 3, 6} a168 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

end BorsukNine.FiniteObstruction

end OAI
