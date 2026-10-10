import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1810 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a121 n105 n116
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n105 (hc.mpr n116)

theorem c1811 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 8, 9} → False := by
  intro a121 a105 a116
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 7} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a105 a116

theorem c1812 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {5, 7, 9} → False := by
  intro a121 n106 n115
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact n106 (hc.mpr n115)

theorem c1813 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {5, 7, 9} → False := by
  intro a121 a106 a115
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a106 a115

theorem c1814 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 7, 8} → False := by
  intro a121 n107 n114
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n107 (hc.mpr n114)

theorem c1815 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {5, 7, 8} → False := by
  intro a121 a107 a114
  have hc := h.complementary {0, 1, 2, 3} {4, 6, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a107 a114

theorem c1816 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n108 n113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact n108 (hc.mpr n113)

theorem c1817 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {5, 6, 9} → False := by
  intro a121 a108 a113
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 8} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 8} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a108 a113

theorem c1818 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  intro a121 n109 n112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n109 (hc.mpr n112)

theorem c1819 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 6, 8} → False := by
  intro a121 a109 a112
  have hc := h.complementary {0, 1, 2, 3} {4, 7, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 7, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a109 a112

theorem c1820 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {5, 6, 7} → False := by
  intro a121 n110 n111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n110 (hc.mpr n111)

theorem c1821 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 6, 7} → False := by
  intro a121 a110 a111
  have hc := h.complementary {0, 1, 2, 3} {4, 8, 9} a121 (by decide) (by decide)
  have he : ( {0, 1, 2, 3} : Finset Labels)ᶜ \ {4, 8, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a110 a111

theorem c1822 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → False := by
  intro a121 n101 n102 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)

theorem c1823 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 5, 7} → T {4, 5, 8} → False := by
  intro a121 a101 a102 a103
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 5} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) a103)

theorem c1824 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → False := by
  intro a121 n101 n102 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1825 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 5, 7} → T {4, 5, 9} → False := by
  intro a121 a101 a102 a104
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 5} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) a104)

theorem c1826 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n101 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1828 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 5, 8} → ¬ T {4, 5, 9} → False := by
  intro a121 n102 n103 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 5} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 5} = {4, 5, 7} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 5} = {4, 5, 8} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c1830 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 8} → False := by
  intro a121 n101 n105 n106
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)

theorem c1831 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 7} → T {4, 6, 8} → False := by
  intro a121 a101 a105 a106
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)

theorem c1832 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1833 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 7} → T {4, 6, 9} → False := by
  intro a121 a101 a105 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c1834 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {4, 6, 8} → ¬ T {4, 6, 9} → False := by
  intro a121 n101 n106 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1835 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {4, 6, 8} → T {4, 6, 9} → False := by
  intro a121 a101 a106 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c1836 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {4, 6, 8} → ¬ T {4, 6, 9} → False := by
  intro a121 n105 n106 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c1837 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {4, 6, 8} → T {4, 6, 9} → False := by
  intro a121 a105 a106 a107
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 6} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) a107)

theorem c1838 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → False := by
  intro a121 n102 n105 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)

theorem c1840 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a121 n102 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c1841 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a121 a102 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1842 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a121 n102 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c1843 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a121 a102 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 7} = {4, 5, 7} by decide)) a102)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1844 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  intro a121 n105 n108 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 7} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c1845 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  intro a121 a105 a108 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 7} {6, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 7} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c1846 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → False := by
  intro a121 n103 n106 n108
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)

theorem c1847 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 6, 8} → T {4, 7, 8} → False := by
  intro a121 a103 a106 a108
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)

theorem c1848 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 6, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n103 n106 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1849 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 6, 8} → T {4, 8, 9} → False := by
  intro a121 a103 a106 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c1850 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n103 n108 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1851 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {4, 7, 8} → T {4, 8, 9} → False := by
  intro a121 a103 a108 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c1852 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  intro a121 n106 n108 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n108 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c1853 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {4, 7, 8} → T {4, 8, 9} → False := by
  intro a121 a106 a108 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) a110)

theorem c1854 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → False := by
  intro a121 n104 n107 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)

theorem c1855 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a121 a104 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c1856 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 6, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n104 n107 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1857 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {4, 6, 9} → T {4, 8, 9} → False := by
  intro a121 a104 a107 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

end BorsukNine.FiniteObstruction

end OAI
