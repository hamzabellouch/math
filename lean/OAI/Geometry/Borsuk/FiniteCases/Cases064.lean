import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c24148 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 1, 9} → ¬ T {1, 3, 9} → ¬ T {1, 8, 9} → False := by
  intro a280 n8 n49 n64
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {1, 9} {0, 3, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) ht)

theorem c24151 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 1, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a280 a8 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 9} {0, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c24152 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {1, 3, 9} → ¬ T {1, 5, 9} → ¬ T {1, 8, 9} → False := by
  intro a280 n49 n58 n64
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {1, 9} {3, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) ht)
  · exact n64 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) ht)

theorem c24153 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {1, 3, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a280 a49 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {1, 9} {3, 5, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c24154 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {1, 3, 5} → ¬ T {3, 5, 8} → False := by
  intro a280 n17 n45 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 5} {0, 1, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c24156 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 5} → ¬ T {1, 3, 5} → ¬ T {3, 5, 9} → False := by
  intro a280 n17 n45 n94
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 5} {0, 1, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) ht)

theorem c24170 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 5, 9} → False := by
  intro a280 n21 n49 n94
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 9} {0, 1, 5} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n94 (Eq.mp (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) ht)

theorem c24172 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 3, 9} → ¬ T {1, 3, 9} → ¬ T {3, 8, 9} → False := by
  intro a280 n21 n49 n100
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {3, 9} {0, 1, 8} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n21 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) ht)

theorem c24179 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → T {0, 5, 8} → T {1, 5, 8} → T {3, 5, 8} → False := by
  intro a280 a29 a57 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 7} {5, 8} {0, 1, 3} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c24180 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a280 n29 n57 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {5, 8} {0, 1, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c24182 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a280 n29 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {5, 8} {0, 3, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c24184 (h : TenSystem T Q) :
    Q {2, 4, 6, 7} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a280 n57 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 7} {5, 8} {1, 3, 9} a280 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c24204 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {0, 1, 5} → ¬ T {3, 7, 9} → False := by
  intro a281 n4 n99
  have hc := h.complementary {2, 4, 6, 8} {0, 1, 5} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 1, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n99)

theorem c24210 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {0, 3, 5} → ¬ T {1, 7, 9} → False := by
  intro a281 n17 n63
  have hc := h.complementary {2, 4, 6, 8} {0, 3, 5} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 3, 5} = {1, 7, 9} := by decide
  rw [he] at hc
  exact n17 (hc.mpr n63)

theorem c24216 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {1, 3, 9} → False := by
  intro a281 n28 n49
  have hc := h.complementary {2, 4, 6, 8} {0, 5, 7} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n49)

theorem c24217 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 5, 7} → T {1, 3, 9} → False := by
  intro a281 a28 a49
  have hc := h.complementary {2, 4, 6, 8} {0, 5, 7} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {1, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a49

theorem c24219 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 5, 9} → T {1, 3, 7} → False := by
  intro a281 a30 a47
  have hc := h.complementary {2, 4, 6, 8} {0, 5, 9} a281 (by decide) (by decide)
  have he : ( {2, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {1, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a30 a47

theorem c24223 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 7} → False := by
  intro a281 a2 a4 a6
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {0, 1} {3, 5, 7} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 1} = {0, 1, 7} by decide)) a6)

theorem c24241 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 5} → T {0, 3, 5} → T {0, 5, 9} → False := by
  intro a281 a4 a17 a30
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {0, 5} {1, 3, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 5} = {0, 5, 9} by decide)) a30)

theorem c24265 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a281 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 3} {0, 5, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24267 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 1, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a281 a2 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 3} {0, 7, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24277 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 9} → False := by
  intro a281 a45 a56 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 5} {3, 7, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) a58)

theorem c24285 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {1, 3, 7} → T {1, 5, 7} → T {1, 7, 9} → False := by
  intro a281 a47 a56 a63
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {1, 7} {3, 5, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 7} = {1, 7, 9} by decide)) a63)

theorem c24304 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → ¬ T {0, 3, 7} → ¬ T {1, 3, 7} → ¬ T {3, 7, 9} → False := by
  intro a281 n19 n47 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 8} {3, 7} {0, 1, 9} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n19 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 7} = {0, 3, 7} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) ht)

theorem c24319 (h : TenSystem T Q) :
    Q {2, 4, 6, 8} → T {0, 5, 7} → T {1, 5, 7} → T {3, 5, 7} → False := by
  intro a281 a28 a56 a92
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 8} {5, 7} {0, 1, 3} a281 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)

theorem c24343 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {5, 7, 8} → False := by
  intro a282 a2 a114
  have hc := h.complementary {2, 4, 6, 9} {0, 1, 3} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a114

theorem c24353 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 3, 7} → T {1, 5, 8} → False := by
  intro a282 a19 a57
  have hc := h.complementary {2, 4, 6, 9} {0, 3, 7} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 3, 7} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a19 a57

theorem c24358 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 7} → False := by
  intro a282 n29 n47
  have hc := h.complementary {2, 4, 6, 9} {0, 5, 8} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n47)

theorem c24359 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 5, 8} → T {1, 3, 7} → False := by
  intro a282 a29 a47
  have hc := h.complementary {2, 4, 6, 9} {0, 5, 8} a282 (by decide) (by decide)
  have he : ( {2, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a47

theorem c24365 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {0, 1, 5} → T {0, 1, 8} → False := by
  intro a282 a2 a4 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {0, 1} {3, 5, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 1} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 1} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c24375 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a282 a2 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {0, 3} {1, 7, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c24405 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 8} → False := by
  intro a282 a2 a45 a48
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {1, 3} {0, 5, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 3} = {1, 3, 8} by decide)) a48)

theorem c24436 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {0, 3, 5} → ¬ T {1, 3, 5} → ¬ T {3, 5, 8} → False := by
  intro a282 n17 n45 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 9} {3, 5} {0, 1, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c24459 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → T {0, 5, 7} → T {1, 5, 7} → T {3, 5, 7} → False := by
  intro a282 a28 a56 a92
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 6, 9} {5, 7} {0, 1, 3} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)

theorem c24464 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 8} → False := by
  intro a282 n56 n92 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 9} {5, 7} {1, 3, 8} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c24468 (h : TenSystem T Q) :
    Q {2, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a282 n29 n57 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 6, 9} {5, 8} {0, 1, 7} a282 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c24515 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {0, 3, 6} → T {0, 3, 9} → False := by
  intro a283 a2 a18 a21
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {0, 3} {1, 6, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 3} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 3} = {0, 3, 9} by decide)) a21)

theorem c24536 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → ¬ T {0, 1, 9} → ¬ T {0, 3, 9} → ¬ T {0, 6, 9} → False := by
  intro a283 n8 n21 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {2, 4, 7, 8} {0, 9} {1, 3, 6} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n8 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) ht)
  · exact n21 (Eq.mp (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) ht)

theorem c24545 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {1, 3, 5} → T {1, 3, 9} → False := by
  intro a283 a2 a45 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {1, 3} {0, 5, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24547 (h : TenSystem T Q) :
    Q {2, 4, 7, 8} → T {0, 1, 3} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a283 a2 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {2, 4, 7, 8} {1, 3} {0, 6, 9} a283 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 3} = {0, 1, 3} by decide)) a2)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c24623 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 1, 3} → T {5, 6, 8} → False := by
  intro a284 a2 a112
  have hc := h.complementary {2, 4, 7, 9} {0, 1, 3} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a2 a112

theorem c24626 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {3, 5, 8} → False := by
  intro a284 n5 n93
  have hc := h.complementary {2, 4, 7, 9} {0, 1, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n93)

theorem c24632 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {1, 5, 8} → False := by
  intro a284 n18 n57
  have hc := h.complementary {2, 4, 7, 9} {0, 3, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n57)

theorem c24633 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → T {0, 3, 6} → T {1, 5, 8} → False := by
  intro a284 a18 a57
  have hc := h.complementary {2, 4, 7, 9} {0, 3, 6} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a18 a57

theorem c24638 (h : TenSystem T Q) :
    Q {2, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 3, 6} → False := by
  intro a284 n29 n46
  have hc := h.complementary {2, 4, 7, 9} {0, 5, 8} a284 (by decide) (by decide)
  have he : ( {2, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 3, 6} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n46)

end BorsukNine.FiniteObstruction

end OAI
