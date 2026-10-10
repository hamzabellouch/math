import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c12895 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {1, 3, 6} → T {1, 3, 7} → False := by
  intro a200 a37 a46 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 3} {2, 6, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c12906 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 6} → ¬ T {1, 3, 6} → ¬ T {1, 4, 6} → False := by
  intro a200 n40 n46 n51
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {1, 6} {2, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) ht)
  · exact n46 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 6} = {1, 3, 6} by decide)) ht)
  · exact n51 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) ht)

theorem c12911 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {1, 4, 6} → T {1, 6, 7} → False := by
  intro a200 a40 a51 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 6} {2, 4, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 6} = {1, 4, 6} by decide)) a51)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 6} = {1, 6, 7} by decide)) a59)

theorem c12914 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 7} → ¬ T {1, 3, 7} → ¬ T {1, 4, 7} → False := by
  intro a200 n41 n47 n52
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {1, 7} {2, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (2 : Labels) {1, 7} = {1, 2, 7} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) ht)
  · exact n52 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) ht)

theorem c12921 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {1, 4, 7} → T {1, 6, 7} → False := by
  intro a200 a47 a52 a59
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {1, 7} {3, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 7} = {1, 4, 7} by decide)) a52)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 7} = {1, 6, 7} by decide)) a59)

theorem c12927 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 3} → T {2, 3, 6} → T {2, 3, 7} → False := by
  intro a200 a37 a67 a68
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {2, 3} {1, 6, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {2, 3} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {2, 3} = {2, 3, 7} by decide)) a68)

theorem c12932 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 4} → ¬ T {2, 3, 4} → ¬ T {2, 4, 7} → False := by
  intro a200 n38 n65 n73
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {2, 4} {1, 3, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n38 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) ht)
  · exact n73 (Eq.mp (congrArg T (show insert (7 : Labels) {2, 4} = {2, 4, 7} by decide)) ht)

theorem c12938 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 6} → ¬ T {2, 3, 6} → ¬ T {2, 4, 6} → False := by
  intro a200 n40 n67 n72
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {2, 6} {1, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n40 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) ht)
  · exact n72 (Eq.mp (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) ht)

theorem c12939 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 2, 6} → T {2, 3, 6} → T {2, 4, 6} → False := by
  intro a200 a40 a67 a72
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {2, 6} {1, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 6} = {1, 2, 6} by decide)) a40)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 6} = {2, 3, 6} by decide)) a67)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {2, 6} = {2, 4, 6} by decide)) a72)

theorem c12948 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 2, 7} → ¬ T {2, 3, 7} → ¬ T {2, 6, 7} → False := by
  intro a200 n41 n68 n80
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {2, 7} {1, 3, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n41 (Eq.mp (congrArg T (show insert (1 : Labels) {2, 7} = {1, 2, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (3 : Labels) {2, 7} = {2, 3, 7} by decide)) ht)
  · exact n80 (Eq.mp (congrArg T (show insert (6 : Labels) {2, 7} = {2, 6, 7} by decide)) ht)

theorem c12964 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 3, 6} → ¬ T {2, 3, 6} → ¬ T {3, 6, 7} → False := by
  intro a200 n46 n67 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {3, 6} {1, 2, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n46 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 6} = {1, 3, 6} by decide)) ht)
  · exact n67 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 6} = {2, 3, 6} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) ht)

theorem c12971 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {2, 3, 7} → T {3, 4, 7} → False := by
  intro a200 a47 a68 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {1, 2, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)

theorem c12972 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 3, 7} → ¬ T {2, 3, 7} → ¬ T {3, 6, 7} → False := by
  intro a200 n47 n68 n95
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {3, 7} {1, 2, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n47 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) ht)
  · exact n68 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 7} = {2, 3, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) ht)

theorem c12975 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {1, 3, 7} → T {3, 4, 7} → T {3, 6, 7} → False := by
  intro a200 a47 a88 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {1, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 7} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)

theorem c12977 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → T {2, 3, 7} → T {3, 4, 7} → T {3, 6, 7} → False := by
  intro a200 a68 a88 a95
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 5, 8, 9} {3, 7} {2, 4, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {3, 7} = {2, 3, 7} by decide)) a68)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {3, 7} = {3, 4, 7} by decide)) a88)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 7} = {3, 6, 7} by decide)) a95)

theorem c12982 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a200 n51 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {4, 6} {1, 3, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n51 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 6} = {1, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c12984 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {2, 4, 6} → ¬ T {3, 4, 6} → ¬ T {4, 6, 7} → False := by
  intro a200 n72 n87 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {4, 6} {2, 3, 7} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n72 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 6} = {2, 4, 6} by decide)) ht)
  · exact n87 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 6} = {3, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)

theorem c12990 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a200 n52 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {4, 7} {1, 3, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n52 (Eq.mp (congrArg T (show insert (1 : Labels) {4, 7} = {1, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c12992 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {2, 4, 7} → ¬ T {3, 4, 7} → ¬ T {4, 6, 7} → False := by
  intro a200 n73 n88 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {4, 7} {2, 3, 6} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n73 (Eq.mp (congrArg T (show insert (2 : Labels) {4, 7} = {2, 4, 7} by decide)) ht)
  · exact n88 (Eq.mp (congrArg T (show insert (3 : Labels) {4, 7} = {3, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)

theorem c12998 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a200 n59 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {6, 7} {1, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c13000 (h : TenSystem T Q) :
    Q {0, 5, 8, 9} → ¬ T {2, 6, 7} → ¬ T {3, 6, 7} → ¬ T {4, 6, 7} → False := by
  intro a200 n80 n95 n105
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 5, 8, 9} {6, 7} {2, 3, 4} a200 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n80 (Eq.mp (congrArg T (show insert (2 : Labels) {6, 7} = {2, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (4 : Labels) {6, 7} = {4, 6, 7} by decide)) ht)

theorem c13015 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 3, 9} → T {2, 4, 5} → False := by
  intro a201 a49 a71
  have hc := h.complementary {0, 6, 7, 8} {1, 3, 9} a201 (by decide) (by decide)
  have he : ( {0, 6, 7, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a49 a71

theorem c13025 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 2, 4} → T {1, 2, 9} → False := by
  intro a201 a37 a38 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 2} {3, 4, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 2} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c13027 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 9} → False := by
  intro a201 a37 a39 a43
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 2} {3, 5, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 2} = {1, 2, 9} by decide)) a43)

theorem c13033 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 3} → T {1, 3, 4} → T {1, 3, 9} → False := by
  intro a201 a37 a44 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 3} {2, 4, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c13057 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 9} → T {1, 3, 9} → T {1, 5, 9} → False := by
  intro a201 a43 a49 a58
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {1, 9} {2, 3, 5} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)

theorem c13071 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 4} → T {2, 3, 4} → T {2, 4, 5} → False := by
  intro a201 a38 a65 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {2, 4} {1, 3, 5} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)

theorem c13089 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → T {1, 2, 9} → T {2, 3, 9} → T {2, 5, 9} → False := by
  intro a201 a43 a70 a79
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 8} {2, 9} {1, 3, 5} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 9} = {1, 2, 9} by decide)) a43)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 9} = {2, 3, 9} by decide)) a70)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 9} = {2, 5, 9} by decide)) a79)

theorem c13096 (h : TenSystem T Q) :
    Q {0, 6, 7, 8} → ¬ T {1, 3, 4} → ¬ T {2, 3, 4} → ¬ T {3, 4, 9} → False := by
  intro a201 n44 n65 n90
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 7, 8} {3, 4} {1, 2, 9} a201 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) ht)
  · exact n65 (Eq.mp (congrArg T (show insert (2 : Labels) {3, 4} = {2, 3, 4} by decide)) ht)
  · exact n90 (Eq.mp (congrArg T (show insert (9 : Labels) {3, 4} = {3, 4, 9} by decide)) ht)

theorem c13144 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {1, 2, 4} → ¬ T {3, 5, 8} → False := by
  intro a202 n38 n93
  have hc := h.complementary {0, 6, 7, 9} {1, 2, 4} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 8} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n93)

theorem c13145 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 2, 4} → T {3, 5, 8} → False := by
  intro a202 a38 a93
  have hc := h.complementary {0, 6, 7, 9} {1, 2, 4} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a38 a93

theorem c13155 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 3, 8} → T {2, 4, 5} → False := by
  intro a202 a48 a71
  have hc := h.complementary {0, 6, 7, 9} {1, 3, 8} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 3, 8} = {2, 4, 5} := by decide
  rw [he] at hc
  exact hc.mp a48 a71

theorem c13160 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {1, 5, 8} → ¬ T {2, 3, 4} → False := by
  intro a202 n57 n65
  have hc := h.complementary {0, 6, 7, 9} {1, 5, 8} a202 (by decide) (by decide)
  have he : ( {0, 6, 7, 9} : Finset Labels)ᶜ \ {1, 5, 8} = {2, 3, 4} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n65)

theorem c13275 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → T {1, 5, 8} → T {2, 5, 8} → T {3, 5, 8} → False := by
  intro a202 a57 a78 a93
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 7, 9} {5, 8} {1, 2, 3} a202 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) a78)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)

theorem c13280 (h : TenSystem T Q) :
    Q {0, 6, 7, 9} → ¬ T {2, 5, 8} → ¬ T {3, 5, 8} → ¬ T {4, 5, 8} → False := by
  intro a202 n78 n93 n103
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 7, 9} {5, 8} {2, 3, 4} a202 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n78 (Eq.mp (congrArg T (show insert (2 : Labels) {5, 8} = {2, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)

theorem c13283 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {4, 5, 7} → False := by
  intro a203 a37 a102
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 3} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 3} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a37 a102

theorem c13284 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 2, 4} → ¬ T {3, 5, 7} → False := by
  intro a203 n38 n92
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 4} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 4} = {3, 5, 7} := by decide
  rw [he] at hc
  exact n38 (hc.mpr n92)

theorem c13286 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 2, 5} → ¬ T {3, 4, 7} → False := by
  intro a203 n39 n88
  have hc := h.complementary {0, 6, 8, 9} {1, 2, 5} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 2, 5} = {3, 4, 7} := by decide
  rw [he] at hc
  exact n39 (hc.mpr n88)

theorem c13298 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 4, 7} → ¬ T {2, 3, 5} → False := by
  intro a203 n52 n66
  have hc := h.complementary {0, 6, 8, 9} {1, 4, 7} a203 (by decide) (by decide)
  have he : ( {0, 6, 8, 9} : Finset Labels)ᶜ \ {1, 4, 7} = {2, 3, 5} := by decide
  rw [he] at hc
  exact n52 (hc.mpr n66)

theorem c13307 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {1, 2, 5} → T {1, 2, 7} → False := by
  intro a203 a37 a39 a41
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {1, 2} {3, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 2} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 2} = {1, 2, 5} by decide)) a39)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 2} = {1, 2, 7} by decide)) a41)

theorem c13315 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 3} → T {1, 3, 5} → T {1, 3, 7} → False := by
  intro a203 a37 a45 a47
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {1, 3} {2, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (2 : Labels) {1, 3} = {1, 2, 3} by decide)) a37)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)

theorem c13316 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → ¬ T {1, 3, 4} → ¬ T {1, 3, 5} → ¬ T {1, 3, 7} → False := by
  intro a203 n44 n45 n47
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 6, 8, 9} {1, 3} {4, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n44 (Eq.mp (congrArg T (show insert (4 : Labels) {1, 3} = {1, 3, 4} by decide)) ht)
  · exact n45 (Eq.mp (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) ht)
  · exact n47 (Eq.mp (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) ht)

theorem c13351 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 2, 4} → T {2, 3, 4} → T {2, 4, 5} → False := by
  intro a203 a38 a65 a71
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {2, 4} {1, 3, 5} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {2, 4} = {1, 2, 4} by decide)) a38)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {2, 4} = {2, 3, 4} by decide)) a65)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {2, 4} = {2, 4, 5} by decide)) a71)

theorem c13379 (h : TenSystem T Q) :
    Q {0, 6, 8, 9} → T {1, 3, 4} → T {3, 4, 5} → T {3, 4, 7} → False := by
  intro a203 a44 a86 a88
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 6, 8, 9} {3, 4} {1, 5, 7} a203 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 4} = {1, 3, 4} by decide)) a44)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 4} = {3, 4, 5} by decide)) a86)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 4} = {3, 4, 7} by decide)) a88)

end BorsukNine.FiniteObstruction

end OAI
