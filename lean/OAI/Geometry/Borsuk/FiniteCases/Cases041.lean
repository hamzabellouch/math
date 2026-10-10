import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c12311 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 4} → T {2, 7, 9} → False := by
  intro a196 a44 a84
  have hc := h.complementary {0, 5, 6, 8} {1, 3, 4} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a44 a84

theorem c12314 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 9} → ¬ T {2, 4, 7} → False := by
  intro a196 n49 n73
  have hc := h.complementary {0, 5, 6, 8} {1, 3, 9} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 4, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n73)

theorem c12316 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 4, 7} → ¬ T {2, 3, 9} → False := by
  intro a196 n52 n70
  have hc := h.complementary {0, 5, 6, 8} {1, 4, 7} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n70)

theorem c12317 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 4, 7} → T {2, 3, 9} → False := by
  intro a196 a52 a70
  have hc := h.complementary {0, 5, 6, 8} {1, 4, 7} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a52 a70

theorem c12321 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 7, 9} → T {2, 3, 4} → False := by
  intro a196 a63 a65
  have hc := h.complementary {0, 5, 6, 8} {1, 7, 9} a196 (by decide) (by decide)
  have he : ( {0, 5, 6, 8} : Finset Labels)ᶜ \ {1, 7, 9} = {2, 3, 4} := by decide
  rw [he] at hc
  exact hc.mp a63 a65

theorem c12327 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 2, 7} → T {1, 2, 9} → False := by
  intro a196 a37 a41 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 2} {3, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c12328 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {1, 2, 7} → ¬ T {1, 2, 9} → False := by
  intro a196 n38 n41 n43
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 2} {4, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) ht)
  · exact n41 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) ht)
  · exact n43 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) ht)

theorem c12331 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a196 a37 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12333 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a196 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 4, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12335 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a196 a37 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 3} {2, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c12336 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {1, 3, 7} → ¬ T {1, 3, 9} → False := by
  intro a196 n44 n47 n49
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 3} {4, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) ht)

theorem c12338 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {1, 3, 4} → ¬ T {1, 4, 7} → False := by
  intro a196 n38 n44 n52
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 4} {2, 3, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) ht)
  · exact n44 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 4} = {1, 4, 7} by decide)) ht)

theorem c12341 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 4} → T {1, 3, 4} → T {1, 4, 9} → False := by
  intro a196 a38 a44 a54
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {1, 4} {2, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 4} = {1, 4, 9} by decide)) a54)

theorem c12354 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 4, 9} → False := by
  intro a196 n43 n49 n54
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 9} {2, 3, 4} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n54 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 9} = {1, 4, 9} by decide)) ht)

theorem c12356 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 9} → ¬ T {1, 3, 9} → ¬ T {1, 7, 9} → False := by
  intro a196 n43 n49 n63
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {1, 9} {2, 3, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) ht)
  · exact n49 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) ht)
  · exact n63 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 9} = {1, 7, 9} by decide)) ht)

theorem c12363 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {2, 3, 4} → T {2, 3, 7} → False := by
  intro a196 a37 a65 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 3} {1, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

theorem c12365 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {2, 3, 4} → T {2, 3, 9} → False := by
  intro a196 a37 a65 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 3} {1, 4, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 3} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12367 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 3} → T {2, 3, 7} → T {2, 3, 9} → False := by
  intro a196 a37 a68 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 3} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c12370 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a196 n38 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 4} {1, 3, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c12372 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 9} → False := by
  intro a196 n38 n65 n75
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 4} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) ht)

theorem c12375 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 4} → T {2, 4, 7} → T {2, 4, 9} → False := by
  intro a196 a38 a73 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 4} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) a75)

theorem c12377 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {2, 3, 4} → T {2, 4, 7} → T {2, 4, 9} → False := by
  intro a196 a65 a73 a75
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 4} {3, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 4} = {2, 4, 9} by decide)) a75)

theorem c12380 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 7, 9} → False := by
  intro a196 n41 n68 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) ht)

theorem c12381 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 2, 7} → T {2, 3, 7} → T {2, 7, 9} → False := by
  intro a196 a41 a68 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) a41)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 7} = {2, 7, 9} by decide)) a84)

theorem c12390 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 2, 9} → ¬ T {2, 4, 9} → ¬ T {2, 7, 9} → False := by
  intro a196 n43 n75 n84
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {2, 9} {1, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n43 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) ht)
  · exact n75 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) ht)

theorem c12393 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {2, 3, 9} → T {2, 4, 9} → T {2, 7, 9} → False := by
  intro a196 a70 a75 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {2, 9} {3, 4, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 9} = {2, 4, 9} by decide)) a75)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c12396 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a196 n44 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {3, 4} {1, 2, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c12397 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 4} → T {2, 3, 4} → T {3, 4, 9} → False := by
  intro a196 a44 a65 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {3, 4} {1, 2, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c12399 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 4} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a196 a44 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {3, 4} {1, 7, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c12410 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 3, 9} → ¬ T {2, 3, 9} → ¬ T {3, 4, 9} → False := by
  intro a196 n49 n70 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {3, 9} {1, 2, 4} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n49 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) ht)
  · exact n70 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) ht)

theorem c12413 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a196 a49 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {3, 9} {1, 2, 7} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c12419 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → T {1, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a196 a52 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 8} {4, 7} {1, 2, 3} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c12422 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 7, 9} → False := by
  intro a196 n52 n88 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {4, 7} {1, 3, 9} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c12436 (h : TenSystem T Q) :
    Q {0, 5, 6, 8} → ¬ T {1, 7, 9} → ¬ T {2, 7, 9} → ¬ T {4, 7, 9} → False := by
  intro a196 n63 n84 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 8} {7, 9} {1, 2, 4} a196 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n63 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) ht)
  · exact n84 (Eq.mp (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) ht)

theorem c12443 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {4, 7, 8} → False := by
  intro a197 a37 a108
  have hc := h.complementary {0, 5, 6, 9} {1, 2, 3} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a37 a108

theorem c12448 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ T {1, 2, 8} → ¬ T {3, 4, 7} → False := by
  intro a197 n42 n88
  have hc := h.complementary {0, 5, 6, 9} {1, 2, 8} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 2, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n42 (hc.mpr n88)

theorem c12459 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 4, 8} → T {2, 3, 7} → False := by
  intro a197 a53 a68
  have hc := h.complementary {0, 5, 6, 9} {1, 4, 8} a197 (by decide) (by decide)
  have he : ( {0, 5, 6, 9} : Finset Labels)ᶜ \ {1, 4, 8} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a53 a68

theorem c12471 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 7} → False := by
  intro a197 a37 a44 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 9} {1, 3} {2, 4, 7} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12510 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a197 n38 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 6, 9} {2, 4} {1, 3, 7} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c12559 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 4, 7} → T {2, 4, 7} → T {3, 4, 7} → False := by
  intro a197 a52 a73 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 9} {4, 7} {1, 2, 3} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) a73)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) a88)

theorem c12575 (h : TenSystem T Q) :
    Q {0, 5, 6, 9} → T {1, 7, 8} → T {2, 7, 8} → T {3, 7, 8} → False := by
  intro a197 a62 a83 a98
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 6, 9} {7, 8} {1, 2, 3} a197 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 8} = {1, 7, 8} by decide)) a62)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 8} = {2, 7, 8} by decide)) a83)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 8} = {3, 7, 8} by decide)) a98)

theorem c12583 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 3} → T {4, 6, 9} → False := by
  intro a198 a37 a107
  have hc := h.complementary {0, 5, 7, 8} {1, 2, 3} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a37 a107

theorem c12587 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 2, 6} → T {3, 4, 9} → False := by
  intro a198 a40 a90
  have hc := h.complementary {0, 5, 7, 8} {1, 2, 6} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 2, 6} = {3, 4, 9} := by decide
  rw [he] at hc
  exact hc.mp a40 a90

theorem c12591 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → T {1, 3, 4} → T {2, 6, 9} → False := by
  intro a198 a44 a82
  have hc := h.complementary {0, 5, 7, 8} {1, 3, 4} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 3, 4} = {2, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a44 a82

theorem c12594 (h : TenSystem T Q) :
    Q {0, 5, 7, 8} → ¬ T {1, 3, 9} → ¬ T {2, 4, 6} → False := by
  intro a198 n49 n72
  have hc := h.complementary {0, 5, 7, 8} {1, 3, 9} a198 (by decide) (by decide)
  have he : ( {0, 5, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 4, 6} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n72)

end BorsukNine.FiniteObstruction

end OAI
