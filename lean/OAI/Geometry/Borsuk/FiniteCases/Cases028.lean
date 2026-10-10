import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c4939 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 3, 9} → T {2, 5, 9} → T {2, 8, 9} → False := by
  intro a143 a70 a79 a85
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 7} {2, 9} {3, 5, 8} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {2, 9} = {2, 8, 9} by decide)) a85)

theorem c4978 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ T {2, 4, 5} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a143 n71 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 7} {4, 5} {2, 8, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n71 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c5003 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {2, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a143 a78 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 7} {5, 8} {2, 4, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c5004 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a143 n93 n103 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 7} {5, 8} {3, 4, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c5005 (h : TenSystem T Q) :
    Q {0, 1, 6, 7} → T {3, 5, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  intro a143 a93 a103 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 7} {5, 8} {3, 4, 9} a143 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c5024 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {2, 3, 5} → ¬ T {4, 7, 9} → False := by
  intro a144 n66 n109
  have hc := h.complementary {0, 1, 6, 8} {2, 3, 5} a144 (by decide) (by decide)
  have he : ( {0, 1, 6, 8} : Finset Labels)ᶜ \ {2, 3, 5} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n66 (hc.mpr n109)

theorem c5028 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {2, 3, 9} → ¬ T {4, 5, 7} → False := by
  intro a144 n70 n102
  have hc := h.complementary {0, 1, 6, 8} {2, 3, 9} a144 (by decide) (by decide)
  have he : ( {0, 1, 6, 8} : Finset Labels)ᶜ \ {2, 3, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact n70 (hc.mpr n102)

theorem c5031 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {2, 4, 5} → T {3, 7, 9} → False := by
  intro a144 a71 a99
  have hc := h.complementary {0, 1, 6, 8} {2, 4, 5} a144 (by decide) (by decide)
  have he : ( {0, 1, 6, 8} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a71 a99

theorem c5089 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 9} → False := by
  intro a144 a86 a88 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {3, 4} {5, 7, 9} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c5115 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 7} → False := by
  intro a144 a71 a86 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {4, 5} {2, 3, 7} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c5137 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → T {3, 4, 9} → T {4, 5, 9} → T {4, 7, 9} → False := by
  intro a144 a90 a104 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 8} {4, 9} {3, 5, 7} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c5142 (h : TenSystem T Q) :
    Q {0, 1, 6, 8} → ¬ T {2, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a144 n77 n102 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 8} {5, 7} {2, 4, 9} a144 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c5171 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 4, 5} → T {3, 7, 8} → False := by
  intro a145 a71 a98
  have hc := h.complementary {0, 1, 6, 9} {2, 4, 5} a145 (by decide) (by decide)
  have he : ( {0, 1, 6, 9} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a71 a98

theorem c5173 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 4, 7} → T {3, 5, 8} → False := by
  intro a145 a73 a93
  have hc := h.complementary {0, 1, 6, 9} {2, 4, 7} a145 (by decide) (by decide)
  have he : ( {0, 1, 6, 9} : Finset Labels)ᶜ \ {2, 4, 7} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a73 a93

theorem c5179 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 5, 8} → T {3, 4, 7} → False := by
  intro a145 a78 a88
  have hc := h.complementary {0, 1, 6, 9} {2, 5, 8} a145 (by decide) (by decide)
  have he : ( {0, 1, 6, 9} : Finset Labels)ᶜ \ {2, 5, 8} = {3, 4, 7} := by decide
  rw [he] at hc
  exact hc.mp a78 a88

theorem c5229 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {3, 4, 5} → T {3, 4, 7} → T {3, 4, 8} → False := by
  intro a145 a86 a88 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {3, 4} {5, 7, 8} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c5255 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 7} → False := by
  intro a145 a71 a86 a102
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {4, 5} {2, 3, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)

theorem c5292 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a145 n93 n103 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c5293 (h : TenSystem T Q) :
    Q {0, 1, 6, 9} → T {3, 5, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  intro a145 a93 a103 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 6, 9} {5, 8} {3, 4, 7} a145 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c5306 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → ¬ T {2, 3, 6} → ¬ T {4, 5, 9} → False := by
  intro a146 n67 n104
  have hc := h.complementary {0, 1, 7, 8} {2, 3, 6} a146 (by decide) (by decide)
  have he : ( {0, 1, 7, 8} : Finset Labels)ᶜ \ {2, 3, 6} = {4, 5, 9} := by decide
  rw [he] at hc
  exact n67 (hc.mpr n104)

theorem c5313 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → T {2, 4, 6} → T {3, 5, 9} → False := by
  intro a146 a72 a94
  have hc := h.complementary {0, 1, 7, 8} {2, 4, 6} a146 (by decide) (by decide)
  have he : ( {0, 1, 7, 8} : Finset Labels)ᶜ \ {2, 4, 6} = {3, 5, 9} := by decide
  rw [he] at hc
  exact hc.mp a72 a94

theorem c5369 (h : TenSystem T Q) :
    Q {0, 1, 7, 8} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 9} → False := by
  intro a146 a86 a87 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 8} {3, 4} {5, 6, 9} a146 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c5442 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ T {2, 3, 4} → ¬ T {5, 6, 8} → False := by
  intro a147 n65 n112
  have hc := h.complementary {0, 1, 7, 9} {2, 3, 4} a147 (by decide) (by decide)
  have he : ( {0, 1, 7, 9} : Finset Labels)ᶜ \ {2, 3, 4} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n65 (hc.mpr n112)

theorem c5449 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 3, 8} → T {4, 5, 6} → False := by
  intro a147 a69 a101
  have hc := h.complementary {0, 1, 7, 9} {2, 3, 8} a147 (by decide) (by decide)
  have he : ( {0, 1, 7, 9} : Finset Labels)ᶜ \ {2, 3, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a69 a101

theorem c5501 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 4, 8} → T {2, 5, 8} → T {2, 6, 8} → False := by
  intro a147 a74 a78 a81
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {2, 8} {4, 5, 6} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 8} = {2, 4, 8} by decide)) a74)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 8} = {2, 6, 8} by decide)) a81)

theorem c5509 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {3, 4, 5} → T {3, 4, 6} → T {3, 4, 8} → False := by
  intro a147 a86 a87 a89
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {3, 4} {5, 6, 8} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)

theorem c5535 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 4, 5} → T {3, 4, 5} → T {4, 5, 6} → False := by
  intro a147 a71 a86 a101
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {4, 5} {2, 3, 6} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 5} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 5} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)

theorem c5571 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → T {2, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a147 a78 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 7, 9} {5, 8} {2, 4, 6} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c5580 (h : TenSystem T Q) :
    Q {0, 1, 7, 9} → ¬ T {3, 6, 8} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → False := by
  intro a147 n96 n106 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 7, 9} {6, 8} {3, 4, 5} a147 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)

theorem c5591 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 4, 5} → T {3, 6, 7} → False := by
  intro a148 a71 a95
  have hc := h.complementary {0, 1, 8, 9} {2, 4, 5} a148 (by decide) (by decide)
  have he : ( {0, 1, 8, 9} : Finset Labels)ᶜ \ {2, 4, 5} = {3, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a71 a95

theorem c5595 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 4, 7} → T {3, 5, 6} → False := by
  intro a148 a73 a91
  have hc := h.complementary {0, 1, 8, 9} {2, 4, 7} a148 (by decide) (by decide)
  have he : ( {0, 1, 8, 9} : Finset Labels)ᶜ \ {2, 4, 7} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a73 a91

theorem c5611 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 3, 4} → T {2, 4, 5} → T {2, 4, 6} → False := by
  intro a148 a65 a71 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 8, 9} {2, 4} {3, 5, 6} a148 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 4} = {2, 4, 6} by decide)) a72)

theorem c5685 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → T {2, 4, 6} → T {3, 4, 6} → T {4, 6, 7} → False := by
  intro a148 a72 a87 a105
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 8, 9} {4, 6} {2, 3, 7} a148 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) a72)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)

theorem c5712 (h : TenSystem T Q) :
    Q {0, 1, 8, 9} → ¬ T {3, 5, 7} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a148 n92 n102 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 8, 9} {5, 7} {3, 4, 6} a148 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c5723 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 6} → T {7, 8, 9} → False := by
  intro a149 a55 a120
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 6} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a55 a120

theorem c5727 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 8} → T {6, 7, 9} → False := by
  intro a149 a57 a118
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 8} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a57 a118

theorem c5728 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 5, 9} → ¬ T {6, 7, 8} → False := by
  intro a149 n58 n117
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n58 (hc.mpr n117)

theorem c5729 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 9} → T {6, 7, 8} → False := by
  intro a149 a58 a117
  have hc := h.complementary {0, 2, 3, 4} {1, 5, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a58 a117

theorem c5731 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 6, 7} → T {5, 8, 9} → False := by
  intro a149 a59 a116
  have hc := h.complementary {0, 2, 3, 4} {1, 6, 7} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a59 a116

theorem c5738 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 7, 9} → ¬ T {5, 6, 8} → False := by
  intro a149 n63 n112
  have hc := h.complementary {0, 2, 3, 4} {1, 7, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n63 (hc.mpr n112)

theorem c5739 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 7, 9} → T {5, 6, 8} → False := by
  intro a149 a63 a112
  have hc := h.complementary {0, 2, 3, 4} {1, 7, 9} a149 (by decide) (by decide)
  have he : ( {0, 2, 3, 4} : Finset Labels)ᶜ \ {1, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a63 a112

theorem c5746 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 5, 6} → ¬ T {1, 5, 8} → ¬ T {1, 5, 9} → False := by
  intro a149 n55 n57 n58
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 4} {1, 5} {6, 8, 9} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n55 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) ht)
  · exact n58 (Eq.mp (congrArg T (show insert (9 : Labels) {1, 5} = {1, 5, 9} by decide)) ht)

theorem c5801 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a149 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 4} {5, 8} {1, 6, 9} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c5848 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → ¬ T {1, 7, 9} → ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a149 n63 n115 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 3, 4} {7, 9} {1, 5, 8} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n63 (Eq.mp (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c5855 (h : TenSystem T Q) :
    Q {0, 2, 3, 4} → T {1, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a149 a64 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 3, 4} {8, 9} {1, 5, 6} a149 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c5863 (h : TenSystem T Q) :
    Q {0, 2, 3, 5} → T {1, 4, 6} → T {7, 8, 9} → False := by
  intro a150 a51 a120
  have hc := h.complementary {0, 2, 3, 5} {1, 4, 6} a150 (by decide) (by decide)
  have he : ( {0, 2, 3, 5} : Finset Labels)ᶜ \ {1, 4, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a51 a120

end BorsukNine.FiniteObstruction

end OAI
