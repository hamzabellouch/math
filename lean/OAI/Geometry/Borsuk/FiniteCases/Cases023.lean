import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c1915 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 6, 9} → T {6, 7, 9} → T {6, 8, 9} → False := by
  intro a121 a107 a118 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {4, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c1916 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n113 n118 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {6, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n113 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) ht)

theorem c1917 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 6, 9} → T {6, 7, 9} → T {6, 8, 9} → False := by
  intro a121 a113 a118 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {6, 9} {5, 7, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c1919 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {5, 7, 8} → T {6, 7, 8} → False := by
  intro a121 a108 a114 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)

theorem c1920 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {5, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n108 n114 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {4, 5, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1922 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 8} → ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n108 n117 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n108 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1923 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a121 a108 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {4, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 8} = {4, 7, 8} by decide)) a108)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c1924 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 8} → ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → False := by
  intro a121 n114 n117 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n114 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) ht)

theorem c1925 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 7, 8} → T {6, 7, 8} → T {7, 8, 9} → False := by
  intro a121 a114 a117 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 8} {5, 6, 9} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 8} = {5, 7, 8} by decide)) a114)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 8} = {6, 7, 8} by decide)) a117)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {7, 8} = {7, 8, 9} by decide)) a120)

theorem c1926 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {5, 7, 9} → ¬ T {6, 7, 9} → False := by
  intro a121 n109 n115 n118
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n109 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) ht)
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)

theorem c1927 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {5, 7, 9} → T {6, 7, 9} → False := by
  intro a121 a109 a115 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) a115)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c1930 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 7, 9} → ¬ T {6, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n109 n118 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n109 (Eq.mp (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c1931 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 7, 9} → T {6, 7, 9} → T {7, 8, 9} → False := by
  intro a121 a109 a118 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {7, 9} {4, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) a120)

theorem c1932 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 7, 9} → ¬ T {6, 7, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n115 n118 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {7, 9} {5, 6, 8} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n115 (Eq.mp (congrArg T (show insert (5 : Labels) {7, 9} = {5, 7, 9} by decide)) ht)
  · exact n118 (Eq.mp (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (8 : Labels) {7, 9} = {7, 8, 9} by decide)) ht)

theorem c1934 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {5, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a121 n110 n116 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c1935 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a121 a110 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 6} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c1937 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {5, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a110 a116 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 5, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1938 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {4, 8, 9} → ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n110 n119 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n110 (Eq.mp (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c1939 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {4, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a110 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {4, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {8, 9} = {4, 8, 9} by decide)) a110)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1940 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → ¬ T {5, 8, 9} → ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → False := by
  intro a121 n116 n119 n120
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 3} {8, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)
  · exact n120 (Eq.mp (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) ht)

theorem c1941 (h : TenSystem T Q) :
    Q {0, 1, 2, 3} → T {5, 8, 9} → T {6, 8, 9} → T {7, 8, 9} → False := by
  intro a121 a116 a119 a120
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 3} {8, 9} {5, 6, 7} a121 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {8, 9} = {7, 8, 9} by decide)) a120)

theorem c1943 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {7, 8, 9} → False := by
  intro a122 a91 a120
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 6} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 6} = {7, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a91 a120

theorem c1946 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 8} → ¬ T {6, 7, 9} → False := by
  intro a122 n93 n118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n93 (hc.mpr n118)

theorem c1947 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 8} → T {6, 7, 9} → False := by
  intro a122 a93 a118
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a93 a118

theorem c1949 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 9} → T {6, 7, 8} → False := by
  intro a122 a94 a117
  have hc := h.complementary {0, 1, 2, 4} {3, 5, 9} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 5, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a94 a117

theorem c1950 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 6, 7} → ¬ T {5, 8, 9} → False := by
  intro a122 n95 n116
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 7} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact n95 (hc.mpr n116)

theorem c1951 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 7} → T {5, 8, 9} → False := by
  intro a122 a95 a116
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 7} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 7} = {5, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a95 a116

theorem c1953 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 8} → T {5, 7, 9} → False := by
  intro a122 a96 a115
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 8} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 8} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a96 a115

theorem c1955 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 9} → T {5, 7, 8} → False := by
  intro a122 a97 a114
  have hc := h.complementary {0, 1, 2, 4} {3, 6, 9} a122 (by decide) (by decide)
  have he : ( {0, 1, 2, 4} : Finset Labels)ᶜ \ {3, 6, 9} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a97 a114

theorem c1967 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a122 a91 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 5} {6, 8, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c1971 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 6} → T {3, 6, 7} → T {3, 6, 8} → False := by
  intro a122 a91 a95 a96
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 6} {5, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) a96)

theorem c1981 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 5, 7} → T {3, 6, 7} → T {3, 7, 9} → False := by
  intro a122 a92 a95 a99
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 7} {5, 6, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) a99)

theorem c2001 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → T {3, 6, 9} → T {3, 7, 9} → T {3, 8, 9} → False := by
  intro a122 a97 a99 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 4} {3, 9} {6, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 9} = {3, 7, 9} by decide)) a99)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c2002 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 6} → ¬ T {5, 6, 7} → ¬ T {5, 6, 8} → False := by
  intro a122 n91 n111 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {5, 6} {3, 7, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n91 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)

theorem c2020 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a122 n93 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {5, 8} {3, 6, 9} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c2034 (h : TenSystem T Q) :
    Q {0, 1, 2, 4} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a122 n95 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 4} {6, 7} {3, 5, 8} a122 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c2084 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 4, 7} → ¬ T {6, 8, 9} → False := by
  intro a123 n88 n119
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 7} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact n88 (hc.mpr n119)

theorem c2085 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 7} → T {6, 8, 9} → False := by
  intro a123 a88 a119
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 7} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 7} = {6, 8, 9} := by decide
  rw [he] at hc
  exact hc.mp a88 a119

theorem c2087 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 8} → T {6, 7, 9} → False := by
  intro a123 a89 a118
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 8} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 8} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a89 a118

theorem c2089 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 9} → T {6, 7, 8} → False := by
  intro a123 a90 a117
  have hc := h.complementary {0, 1, 2, 5} {3, 4, 9} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 4, 9} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a90 a117

theorem c2098 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 7, 9} → ¬ T {4, 6, 8} → False := by
  intro a123 n99 n106
  have hc := h.complementary {0, 1, 2, 5} {3, 7, 9} a123 (by decide) (by decide)
  have he : ( {0, 1, 2, 5} : Finset Labels)ᶜ \ {3, 7, 9} = {4, 6, 8} := by decide
  rw [he] at hc
  exact n99 (hc.mpr n106)

theorem c2107 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 6} → T {3, 4, 8} → T {3, 4, 9} → False := by
  intro a123 a87 a89 a90
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {3, 4} {6, 8, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 4} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 4} = {3, 4, 8} by decide)) a89)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) a90)

theorem c2113 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 6} → T {3, 6, 7} → T {3, 6, 9} → False := by
  intro a123 a87 a95 a97
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {3, 6} {4, 7, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 6} = {3, 4, 6} by decide)) a87)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 6} = {3, 6, 9} by decide)) a97)

theorem c2122 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → ¬ T {3, 4, 7} → ¬ T {3, 7, 8} → ¬ T {3, 7, 9} → False := by
  intro a123 n88 n98 n99
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 1, 2, 5} {3, 7} {4, 8, 9} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n88 (Eq.mp (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) ht)
  · exact n98 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 7} = {3, 7, 8} by decide)) ht)
  · exact n99 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 7} = {3, 7, 9} by decide)) ht)

theorem c2137 (h : TenSystem T Q) :
    Q {0, 1, 2, 5} → T {3, 4, 9} → T {3, 6, 9} → T {3, 8, 9} → False := by
  intro a123 a90 a97 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 1, 2, 5} {3, 9} {4, 6, 8} a123 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 9} = {3, 4, 9} by decide)) a90)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

end BorsukNine.FiniteObstruction

end OAI
