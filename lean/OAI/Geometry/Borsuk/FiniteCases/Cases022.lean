import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1858 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n104 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 9} = {4, 5, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1860 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {4, 7, 9} → ¬ T {4, 8, 9} → False := by
  intro a121 n107 n109 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) ht)

theorem c1861 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {4, 7, 9} → T {4, 8, 9} → False := by
  intro a121 a107 a109 a110
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {4, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {4, 9} = {4, 8, 9} by decide)) a110)

theorem c1865 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a121 a101 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c1866 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 6} → ¬ T {5, 6, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n101 n112 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 6} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n101 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) ht)

theorem c1867 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 6} → T {5, 6, 8} → T {5, 6, 9} → False := by
  intro a121 a101 a112 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 6} = {4, 5, 6} by decide)) a101)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c1868 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → ¬ T {5, 6, 9} → False := by
  intro a121 n111 n112 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) ht)

theorem c1869 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 7} → T {5, 6, 8} → T {5, 6, 9} → False := by
  intro a121 a111 a112 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 6} {7, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c1870 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → ¬ T {5, 7, 8} → False := by
  intro a121 n102 n111 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 7} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 7} = {5, 7, 8} by decide)) ht)

theorem c1872 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 7} → ¬ T {5, 6, 7} → ¬ T {5, 7, 9} → False := by
  intro a121 n102 n111 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 7} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n102 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 7} = {4, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) ht)

theorem c1878 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a121 n103 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c1879 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a121 a103 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c1880 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n103 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1881 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1882 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n103 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1883 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a103 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1884 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → ¬ T {5, 8, 9} → False := by
  intro a121 n112 n114 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c1885 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  intro a121 a112 a114 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 8} {6, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c1886 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {5, 6, 9} → ¬ T {5, 7, 9} → False := by
  intro a121 n104 n113 n115
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) ht)

theorem c1887 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {5, 6, 9} → T {5, 7, 9} → False := by
  intro a121 a104 a113 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c1889 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 5, 9} → T {5, 6, 9} → T {5, 8, 9} → False := by
  intro a121 a104 a113 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 9} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) a104)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c1890 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 5, 9} → ¬ T {5, 7, 9} → ¬ T {5, 8, 9} → False := by
  intro a121 n104 n115 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {5, 9} {4, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n104 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 9} = {4, 5, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) ht)

theorem c1893 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  intro a121 a113 a115 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {5, 9} {6, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c1894 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a121 n105 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c1895 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 6, 7} → T {6, 7, 8} → False := by
  intro a121 a105 a111 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c1896 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  intro a121 n105 n111 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c1897 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {5, 6, 7} → T {6, 7, 9} → False := by
  intro a121 a105 a111 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c1898 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 7} → ¬ T {6, 7, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n105 n117 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c1899 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  intro a121 a105 a117 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {4, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c1900 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → ¬ T {6, 7, 9} → False := by
  intro a121 n111 n117 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) ht)

theorem c1901 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  intro a121 a111 a117 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 7} {5, 8, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c1902 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 7, 8} → False := by
  intro a121 n106 n112 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)

theorem c1903 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {5, 6, 8} → T {6, 7, 8} → False := by
  intro a121 a106 a112 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 8} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)

theorem c1904 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {5, 6, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n106 n112 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c1906 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 8} → ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n106 n117 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n106 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c1907 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 8} → T {6, 7, 8} → T {6, 8, 9} → False := by
  intro a121 a106 a117 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 8} {4, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 8} = {4, 6, 8} by decide)) a106)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) a119)

theorem c1908 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 8} → ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → False := by
  intro a121 n112 n117 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 8} {5, 7, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n112 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 8} = {5, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (9 : Labels) {6, 8} = {6, 8, 9} by decide)) ht)

theorem c1910 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → False := by
  intro a121 n107 n113 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)

theorem c1911 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {5, 6, 9} → T {6, 7, 9} → False := by
  intro a121 a107 a113 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c1912 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {5, 6, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n107 n113 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

theorem c1913 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {5, 6, 9} → T {6, 8, 9} → False := by
  intro a121 a107 a113 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {4, 5, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c1914 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n107 n118 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {4, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n107 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
