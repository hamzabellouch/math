import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c19282 (h : TenSystem T Q) :
    Q {1, 4, 6, 7} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 8, 9} → False := by
  intro a245 n29 n93 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 7} {5, 8} {0, 3, 9} a245 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c19303 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {5, 7, 9} → False := by
  intro a246 a9 a115
  have hc := h.complementary {1, 4, 6, 8} {0, 2, 3} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a115

theorem c19309 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 9} → T {3, 5, 7} → False := by
  intro a246 a15 a92
  have hc := h.complementary {1, 4, 6, 8} {0, 2, 9} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 2, 9} = {3, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a15 a92

theorem c19316 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {2, 3, 9} → False := by
  intro a246 n28 n70
  have hc := h.complementary {1, 4, 6, 8} {0, 5, 7} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact n28 (hc.mpr n70)

theorem c19317 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 5, 7} → T {2, 3, 9} → False := by
  intro a246 a28 a70
  have hc := h.complementary {1, 4, 6, 8} {0, 5, 7} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 5, 7} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a28 a70

theorem c19320 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 7, 9} → ¬ T {2, 3, 5} → False := by
  intro a246 n35 n66
  have hc := h.complementary {1, 4, 6, 8} {0, 7, 9} a246 (by decide) (by decide)
  have he : ( {1, 4, 6, 8} : Finset Labels)ᶜ \ {0, 7, 9} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n35 (hc.mpr n66)

theorem c19323 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a246 a9 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 2} {3, 5, 7} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19325 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 9} → False := by
  intro a246 a9 a11 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 2} {3, 5, 9} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c19357 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 9} → T {0, 3, 9} → T {0, 7, 9} → False := by
  intro a246 a15 a21 a35
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {0, 9} {2, 3, 7} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 9} = {0, 7, 9} by decide)) a35)

theorem c19365 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 9} → False := by
  intro a246 a9 a66 a70
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {2, 3} {0, 5, 9} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {2, 3} = {2, 3, 9} by decide)) a70)

theorem c19413 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 3, 9} → T {2, 3, 9} → T {3, 7, 9} → False := by
  intro a246 a21 a70 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {3, 9} {0, 2, 7} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {3, 9} = {0, 3, 9} by decide)) a21)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)

theorem c19422 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a246 n28 n92 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 8} {5, 7} {0, 3, 9} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c19435 (h : TenSystem T Q) :
    Q {1, 4, 6, 8} → T {0, 7, 9} → T {2, 7, 9} → T {3, 7, 9} → False := by
  intro a246 a35 a84 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 8} {7, 9} {0, 2, 3} a246 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {7, 9} = {3, 7, 9} by decide)) a99)

theorem c19449 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 8} → T {3, 5, 7} → False := by
  intro a247 a14 a92
  have hc := h.complementary {1, 4, 6, 9} {0, 2, 8} a247 (by decide) (by decide)
  have he : ( {1, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a14 a92

theorem c19459 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 5, 8} → T {2, 3, 7} → False := by
  intro a247 a29 a68
  have hc := h.complementary {1, 4, 6, 9} {0, 5, 8} a247 (by decide) (by decide)
  have he : ( {1, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a68

theorem c19463 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 3} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a247 a9 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 9} {0, 2} {3, 5, 7} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19475 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → T {0, 2, 3} → T {0, 3, 7} → T {0, 3, 8} → False := by
  intro a247 a9 a19 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 6, 9} {0, 3} {2, 7, 8} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 3} = {0, 3, 7} by decide)) a19)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19536 (h : TenSystem T Q) :
    Q {1, 4, 6, 9} → ¬ T {0, 3, 5} → ¬ T {2, 3, 5} → ¬ T {3, 5, 8} → False := by
  intro a247 n17 n66 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 6, 9} {3, 5} {0, 2, 8} a247 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n17 (Eq.mp (congrArg T (show insert (0 : Labels) {3, 5} = {0, 3, 5} by decide)) ht)
  · exact n66 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 5} = {2, 3, 5} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c19583 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → T {0, 2, 3} → T {5, 6, 9} → False := by
  intro a248 a9 a113
  have hc := h.complementary {1, 4, 7, 8} {0, 2, 3} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a9 a113

theorem c19584 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → ¬ T {0, 2, 5} → ¬ T {3, 6, 9} → False := by
  intro a248 n11 n97
  have hc := h.complementary {1, 4, 7, 8} {0, 2, 5} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 9} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n97)

theorem c19597 (h : TenSystem T Q) :
    Q {1, 4, 7, 8} → T {0, 5, 6} → T {2, 3, 9} → False := by
  intro a248 a27 a70
  have hc := h.complementary {1, 4, 7, 8} {0, 5, 6} a248 (by decide) (by decide)
  have he : ( {1, 4, 7, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {2, 3, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a70

theorem c19723 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {5, 6, 8} → False := by
  intro a249 a9 a112
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 3} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 3} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a9 a112

theorem c19724 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 5} → ¬ T {3, 6, 8} → False := by
  intro a249 n11 n96
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n11 (hc.mpr n96)

theorem c19725 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 5} → T {3, 6, 8} → False := by
  intro a249 a11 a96
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {3, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a96

theorem c19726 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {3, 5, 8} → False := by
  intro a249 n12 n93
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n93)

theorem c19727 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 6} → T {3, 5, 8} → False := by
  intro a249 a12 a93
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a93

theorem c19728 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 8} → ¬ T {3, 5, 6} → False := by
  intro a249 n14 n91
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n91)

theorem c19729 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 8} → T {3, 5, 6} → False := by
  intro a249 a14 a91
  have hc := h.complementary {1, 4, 7, 9} {0, 2, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {3, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a91

theorem c19731 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 5} → T {2, 6, 8} → False := by
  intro a249 a17 a81
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 5} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a17 a81

theorem c19732 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 3, 6} → ¬ T {2, 5, 8} → False := by
  intro a249 n18 n78
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 6} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n18 (hc.mpr n78)

theorem c19735 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 8} → T {2, 5, 6} → False := by
  intro a249 a20 a76
  have hc := h.complementary {1, 4, 7, 9} {0, 3, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 3, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a20 a76

theorem c19738 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 3, 6} → False := by
  intro a249 n29 n67
  have hc := h.complementary {1, 4, 7, 9} {0, 5, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n67)

theorem c19739 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 5, 8} → T {2, 3, 6} → False := by
  intro a249 a29 a67
  have hc := h.complementary {1, 4, 7, 9} {0, 5, 8} a249 (by decide) (by decide)
  have he : ( {1, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {2, 3, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a67

theorem c19753 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {0, 3, 5} → T {0, 3, 8} → False := by
  intro a249 a9 a17 a20
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {0, 3} {2, 5, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 3} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 3} = {0, 3, 8} by decide)) a20)

theorem c19773 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 3, 6} → T {0, 5, 6} → T {0, 6, 8} → False := by
  intro a249 a18 a27 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {0, 6} {3, 5, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 6} = {0, 3, 6} by decide)) a18)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) a32)

theorem c19783 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 2, 3} → T {2, 3, 5} → T {2, 3, 6} → False := by
  intro a249 a9 a66 a67
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {2, 3} {0, 5, 6} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 3} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 3} = {2, 3, 5} by decide)) a66)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)

theorem c19798 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 5, 6} → False := by
  intro a249 n12 n67 n76
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {2, 6} {0, 3, 5} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n76 (Eq.mp (congrArg T (show insert (5 : Labels) {2, 6} = {2, 5, 6} by decide)) ht)

theorem c19800 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 6, 8} → False := by
  intro a249 n12 n67 n81
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {2, 6} {0, 3, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n12 (Eq.mp (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n81 (Eq.mp (congrArg T (show insert (8 : Labels) {2, 6} = {2, 6, 8} by decide)) ht)

theorem c19842 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 6} → ¬ T {3, 5, 6} → ¬ T {5, 6, 8} → False := by
  intro a249 n27 n91 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {5, 6} {0, 3, 8} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c19847 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → T {0, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a249 a29 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 7, 9} {5, 8} {0, 2, 3} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c19848 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {2, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a249 n29 n78 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {5, 8} {0, 2, 6} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c19850 (h : TenSystem T Q) :
    Q {1, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a249 n29 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 4, 7, 9} {5, 8} {0, 3, 6} a249 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c19880 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → ¬ T {0, 6, 7} → ¬ T {2, 3, 5} → False := by
  intro a250 n31 n66
  have hc := h.complementary {1, 4, 8, 9} {0, 6, 7} a250 (by decide) (by decide)
  have he : ( {1, 4, 8, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n66)

theorem c19887 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 3} → T {0, 2, 6} → T {0, 2, 7} → False := by
  intro a250 a9 a12 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 2} {3, 6, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 2} = {0, 2, 3} by decide)) a9)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c19899 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 5} → T {0, 3, 5} → T {0, 5, 6} → False := by
  intro a250 a11 a17 a27
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 5} {2, 3, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 5} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {0, 5} = {0, 3, 5} by decide)) a17)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 5} = {0, 5, 6} by decide)) a27)

theorem c19919 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 7} → T {0, 5, 7} → T {0, 6, 7} → False := by
  intro a250 a13 a28 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {0, 7} {2, 5, 6} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 7} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 7} = {0, 5, 7} by decide)) a28)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 7} = {0, 6, 7} by decide)) a31)

theorem c19941 (h : TenSystem T Q) :
    Q {1, 4, 8, 9} → T {0, 2, 6} → T {2, 3, 6} → T {2, 6, 7} → False := by
  intro a250 a12 a67 a80
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 4, 8, 9} {2, 6} {0, 3, 7} a250 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {2, 6} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 6} = {2, 6, 7} by decide)) a80)

end BorsukNine.FiniteObstruction

end OAI
