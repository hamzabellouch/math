import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c27117 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {1, 2, 9} → T {2, 5, 9} → T {2, 7, 9} → False := by
  intro a301 a43 a79 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {2, 9} {1, 5, 7} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 9} = {2, 7, 9} by decide)) a84)

theorem c27122 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → ¬ T {0, 5, 7} → ¬ T {2, 5, 7} → ¬ T {5, 7, 9} → False := by
  intro a301 n28 n77 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 8} {5, 7} {0, 2, 9} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n28 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 7} = {0, 5, 7} by decide)) ht)
  · exact n77 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 7} = {2, 5, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c27135 (h : TenSystem T Q) :
    Q {3, 4, 6, 8} → T {0, 7, 9} → T {1, 7, 9} → T {2, 7, 9} → False := by
  intro a301 a35 a63 a84
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 8} {7, 9} {0, 1, 2} a301 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {7, 9} = {1, 7, 9} by decide)) a63)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {7, 9} = {2, 7, 9} by decide)) a84)

theorem c27143 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {5, 7, 8} → False := by
  intro a302 a1 a114
  have hc := h.complementary {3, 4, 6, 9} {0, 1, 2} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a114

theorem c27151 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 2, 5} → T {1, 7, 8} → False := by
  intro a302 a11 a62
  have hc := h.complementary {3, 4, 6, 9} {0, 2, 5} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 5} = {1, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a11 a62

theorem c27152 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 2, 7} → ¬ T {1, 5, 8} → False := by
  intro a302 n13 n57
  have hc := h.complementary {3, 4, 6, 9} {0, 2, 7} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 7} = {1, 5, 8} := by decide
  rw [he] at hc
  exact n13 (hc.mpr n57)

theorem c27155 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 2, 8} → T {1, 5, 7} → False := by
  intro a302 a14 a56
  have hc := h.complementary {3, 4, 6, 9} {0, 2, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a14 a56

theorem c27158 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 7} → False := by
  intro a302 n29 n41
  have hc := h.complementary {3, 4, 6, 9} {0, 5, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n41)

theorem c27159 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 5, 8} → T {1, 2, 7} → False := by
  intro a302 a29 a41
  have hc := h.complementary {3, 4, 6, 9} {0, 5, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a41

theorem c27160 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 7, 8} → ¬ T {1, 2, 5} → False := by
  intro a302 n34 n39
  have hc := h.complementary {3, 4, 6, 9} {0, 7, 8} a302 (by decide) (by decide)
  have he : ( {3, 4, 6, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n34 (hc.mpr n39)

theorem c27171 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 7} → False := by
  intro a302 a1 a11 a13
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {0, 2} {1, 5, 7} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)

theorem c27175 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {0, 2, 7} → T {0, 2, 8} → False := by
  intro a302 a1 a13 a14
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {0, 2} {1, 7, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) a13)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) a14)

theorem c27176 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 2, 5} → ¬ T {0, 2, 7} → ¬ T {0, 2, 8} → False := by
  intro a302 n11 n13 n14
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 9} {0, 2} {5, 7, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n11 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) ht)
  · exact n13 (Eq.mp (congrArg T (show insert (7 : Labels) {0, 2} = {0, 2, 7} by decide)) ht)
  · exact n14 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 2} = {0, 2, 8} by decide)) ht)

theorem c27205 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 8} → False := by
  intro a302 a1 a39 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {1, 2} {0, 5, 8} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c27267 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → T {0, 5, 8} → T {1, 5, 8} → T {2, 5, 8} → False := by
  intro a302 a29 a57 a78
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 6, 9} {5, 8} {0, 1, 2} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)

theorem c27268 (h : TenSystem T Q) :
    Q {3, 4, 6, 9} → ¬ T {0, 5, 8} → ¬ T {1, 5, 8} → ¬ T {5, 7, 8} → False := by
  intro a302 n29 n57 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 6, 9} {5, 8} {0, 1, 7} a302 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c27292 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {0, 2, 6} → ¬ T {1, 5, 9} → False := by
  intro a303 n12 n58
  have hc := h.complementary {3, 4, 7, 8} {0, 2, 6} a303 (by decide) (by decide)
  have he : ( {3, 4, 7, 8} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 9} := by decide
  rw [he] at hc
  exact n12 (hc.mpr n58)

theorem c27300 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {0, 6, 9} → ¬ T {1, 2, 5} → False := by
  intro a303 n33 n39
  have hc := h.complementary {3, 4, 7, 8} {0, 6, 9} a303 (by decide) (by decide)
  have he : ( {3, 4, 7, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n39)

theorem c27311 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {0, 2, 5} → T {0, 2, 6} → False := by
  intro a303 a1 a11 a12
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {0, 2} {1, 5, 6} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 2} = {0, 2, 5} by decide)) a11)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)

theorem c27315 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {0, 2, 6} → T {0, 2, 9} → False := by
  intro a303 a1 a12 a15
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {0, 2} {1, 6, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 2} = {0, 2, 6} by decide)) a12)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {0, 2} = {0, 2, 9} by decide)) a15)

theorem c27328 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 9} → False := by
  intro a303 n5 n12 n33
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 8} {0, 6} {1, 2, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n33 (Eq.mp (congrArg T (show insert (9 : Labels) {0, 6} = {0, 6, 9} by decide)) ht)

theorem c27335 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 9} → T {0, 2, 9} → T {0, 5, 9} → False := by
  intro a303 a8 a15 a30
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {0, 9} {1, 2, 5} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 9} = {0, 1, 9} by decide)) a8)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 9} = {0, 2, 9} by decide)) a15)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 9} = {0, 5, 9} by decide)) a30)

theorem c27347 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 9} → False := by
  intro a303 a1 a40 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {1, 2} {0, 6, 9} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c27351 (h : TenSystem T Q) :
    Q {3, 4, 7, 8} → T {0, 1, 5} → T {1, 2, 5} → T {1, 5, 6} → False := by
  intro a303 a4 a39 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 8} {1, 5} {0, 2, 6} a303 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

theorem c27423 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {5, 6, 8} → False := by
  intro a304 a1 a112
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 2} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 2} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a1 a112

theorem c27424 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 5} → ¬ T {2, 6, 8} → False := by
  intro a304 n4 n81
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 5} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 5} = {2, 6, 8} := by decide
  rw [he] at hc
  exact n4 (hc.mpr n81)

theorem c27426 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {2, 5, 8} → False := by
  intro a304 n5 n78
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact n5 (hc.mpr n78)

theorem c27427 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 6} → T {2, 5, 8} → False := by
  intro a304 a5 a78
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 6} = {2, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a5 a78

theorem c27428 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {2, 5, 6} → False := by
  intro a304 n7 n76
  have hc := h.complementary {3, 4, 7, 9} {0, 1, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 1, 8} = {2, 5, 6} := by decide
  rw [he] at hc
  exact n7 (hc.mpr n76)

theorem c27433 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 6} → T {1, 5, 8} → False := by
  intro a304 a12 a57
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 6} = {1, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a12 a57

theorem c27434 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 2, 8} → ¬ T {1, 5, 6} → False := by
  intro a304 n14 n55
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 6} := by decide
  rw [he] at hc
  exact n14 (hc.mpr n55)

theorem c27435 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 8} → T {1, 5, 6} → False := by
  intro a304 a14 a55
  have hc := h.complementary {3, 4, 7, 9} {0, 2, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 2, 8} = {1, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a14 a55

theorem c27437 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 5, 6} → T {1, 2, 8} → False := by
  intro a304 a27 a42
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 6} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {1, 2, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a42

theorem c27438 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 5, 8} → ¬ T {1, 2, 6} → False := by
  intro a304 n29 n40
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n40)

theorem c27439 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 5, 8} → T {1, 2, 6} → False := by
  intro a304 a29 a40
  have hc := h.complementary {3, 4, 7, 9} {0, 5, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {1, 2, 6} := by decide
  rw [he] at hc
  exact hc.mp a29 a40

theorem c27440 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 6, 8} → ¬ T {1, 2, 5} → False := by
  intro a304 n32 n39
  have hc := h.complementary {3, 4, 7, 9} {0, 6, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n39)

theorem c27441 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 6, 8} → T {1, 2, 5} → False := by
  intro a304 a32 a39
  have hc := h.complementary {3, 4, 7, 9} {0, 6, 8} a304 (by decide) (by decide)
  have he : ( {3, 4, 7, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {1, 2, 5} := by decide
  rw [he] at hc
  exact hc.mp a32 a39

theorem c27447 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {0, 1, 6} → T {0, 1, 8} → False := by
  intro a304 a1 a5 a7
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {0, 1} {2, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 1} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 1} = {0, 1, 6} by decide)) a5)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 1} = {0, 1, 8} by decide)) a7)

theorem c27466 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 5, 6} → False := by
  intro a304 n5 n12 n27
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 6} {1, 2, 5} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n27 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) ht)

theorem c27468 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 6} → ¬ T {0, 2, 6} → ¬ T {0, 6, 8} → False := by
  intro a304 n5 n12 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 6} {1, 2, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n5 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 6} = {0, 1, 6} by decide)) ht)
  · exact n12 (Eq.mp (congrArg T (show insert (2 : Labels) {0, 6} = {0, 2, 6} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (8 : Labels) {0, 6} = {0, 6, 8} by decide)) ht)

theorem c27478 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {0, 1, 8} → ¬ T {0, 5, 8} → ¬ T {0, 6, 8} → False := by
  intro a304 n7 n29 n32
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {0, 8} {1, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n7 (Eq.mp (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) ht)
  · exact n29 (Eq.mp (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) ht)
  · exact n32 (Eq.mp (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) ht)

theorem c27479 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a304 a7 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {0, 8} {1, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {0, 8} = {0, 1, 8} by decide)) a7)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c27481 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 2, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a304 a14 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {0, 8} {2, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {0, 8} = {0, 2, 8} by decide)) a14)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c27483 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {1, 2, 5} → T {1, 2, 6} → False := by
  intro a304 a1 a39 a40
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 2} {0, 5, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)

theorem c27487 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 2} → T {1, 2, 6} → T {1, 2, 8} → False := by
  intro a304 a1 a40 a42
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 2} {0, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 2} = {0, 1, 2} by decide)) a1)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) a42)

theorem c27488 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → ¬ T {1, 2, 5} → ¬ T {1, 2, 6} → ¬ T {1, 2, 8} → False := by
  intro a304 n39 n40 n42
  obtain ⟨w, hw, ht⟩ := three_pos h {3, 4, 7, 9} {1, 2} {5, 6, 8} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n39 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) ht)
  · exact n40 (Eq.mp (congrArg T (show insert (6 : Labels) {1, 2} = {1, 2, 6} by decide)) ht)
  · exact n42 (Eq.mp (congrArg T (show insert (8 : Labels) {1, 2} = {1, 2, 8} by decide)) ht)

theorem c27491 (h : TenSystem T Q) :
    Q {3, 4, 7, 9} → T {0, 1, 5} → T {1, 2, 5} → T {1, 5, 6} → False := by
  intro a304 a4 a39 a55
  obtain ⟨w, hw, ht⟩ := three_neg h {3, 4, 7, 9} {1, 5} {0, 2, 6} a304 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {1, 5} = {0, 1, 5} by decide)) a4)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 5} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)

end BorsukNine.FiniteObstruction

end OAI
