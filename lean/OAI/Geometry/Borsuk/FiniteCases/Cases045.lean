import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c13996 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 6, 8} → ¬ T {4, 5, 9} → False := by
  intro a208 n32 n104
  have hc := h.complementary {1, 2, 3, 7} {0, 6, 8} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 6, 8} = {4, 5, 9} := by decide
  rw [he] at hc
  exact n32 (hc.mpr n104)

theorem c13998 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 6, 9} → ¬ T {4, 5, 8} → False := by
  intro a208 n33 n103
  have hc := h.complementary {1, 2, 3, 7} {0, 6, 9} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 6, 9} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n33 (hc.mpr n103)

theorem c14001 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 8, 9} → T {4, 5, 6} → False := by
  intro a208 a36 a101
  have hc := h.complementary {1, 2, 3, 7} {0, 8, 9} a208 (by decide) (by decide)
  have he : ( {1, 2, 3, 7} : Finset Labels)ᶜ \ {0, 8, 9} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a36 a101

theorem c14027 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 8} → T {0, 5, 8} → T {0, 6, 8} → False := by
  intro a208 a25 a29 a32
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {0, 8} {4, 5, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 8} = {0, 4, 8} by decide)) a25)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 8} = {0, 6, 8} by decide)) a32)

theorem c14039 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 4, 9} → T {0, 6, 9} → T {0, 8, 9} → False := by
  intro a208 a26 a33 a36
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {0, 9} {4, 6, 8} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 9} = {0, 8, 9} by decide)) a36)

theorem c14052 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 9} → False := by
  intro a208 n23 n101 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {4, 6} {0, 5, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c14062 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 4, 8} → ¬ T {4, 6, 8} → ¬ T {4, 8, 9} → False := by
  intro a208 n25 n106 n110
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {4, 8} {0, 6, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n25 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 8} = {0, 4, 8} by decide)) ht)
  · exact n106 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 8} = {4, 6, 8} by decide)) ht)
  · exact n110 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 8} = {4, 8, 9} by decide)) ht)

theorem c14078 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 5, 6} → ¬ T {5, 6, 8} → ¬ T {5, 6, 9} → False := by
  intro a208 n27 n112 n113
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {5, 6} {0, 8, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n27 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 6} = {0, 5, 6} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) ht)
  · exact n113 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) ht)

theorem c14082 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 5, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a208 n29 n103 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {5, 8} {0, 4, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n103 (Eq.mp (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c14083 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {4, 5, 8} → T {5, 6, 8} → False := by
  intro a208 a29 a103 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 8} {0, 4, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {5, 8} = {4, 5, 8} by decide)) a103)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c14086 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → ¬ T {0, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 8, 9} → False := by
  intro a208 n29 n112 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 7} {5, 8} {0, 6, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n29 (Eq.mp (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) ht)

theorem c14087 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a208 a29 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 8} {0, 6, 9} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 8} = {0, 5, 8} by decide)) a29)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c14095 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 5, 9} → T {5, 6, 9} → T {5, 8, 9} → False := by
  intro a208 a30 a113 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {5, 9} {0, 6, 8} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {5, 9} = {0, 5, 9} by decide)) a30)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 9} = {5, 8, 9} by decide)) a116)

theorem c14107 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 6, 9} → T {4, 6, 9} → T {5, 6, 9} → False := by
  intro a208 a33 a107 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {6, 9} {0, 4, 5} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {6, 9} = {5, 6, 9} by decide)) a113)

theorem c14109 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 6, 9} → T {4, 6, 9} → T {6, 8, 9} → False := by
  intro a208 a33 a107 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {6, 9} {0, 4, 8} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {6, 9} = {0, 6, 9} by decide)) a33)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {6, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 9} = {6, 8, 9} by decide)) a119)

theorem c14119 (h : TenSystem T Q) :
    Q {1, 2, 3, 7} → T {0, 8, 9} → T {5, 8, 9} → T {6, 8, 9} → False := by
  intro a208 a36 a116 a119
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 7} {8, 9} {0, 5, 6} a208 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {8, 9} = {0, 8, 9} by decide)) a36)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) a119)

theorem c14122 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 5} → ¬ T {6, 7, 9} → False := by
  intro a209 n22 n118
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 5} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n118)

theorem c14123 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 5} → T {6, 7, 9} → False := by
  intro a209 a22 a118
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 5} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a22 a118

theorem c14125 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 6} → T {5, 7, 9} → False := by
  intro a209 a23 a115
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a23 a115

theorem c14127 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 7} → T {5, 6, 9} → False := by
  intro a209 a24 a113
  have hc := h.complementary {1, 2, 3, 8} {0, 4, 7} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 9} := by decide
  rw [he] at hc
  exact hc.mp a24 a113

theorem c14130 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 5, 6} → ¬ T {4, 7, 9} → False := by
  intro a209 n27 n109
  have hc := h.complementary {1, 2, 3, 8} {0, 5, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact n27 (hc.mpr n109)

theorem c14131 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 5, 6} → T {4, 7, 9} → False := by
  intro a209 a27 a109
  have hc := h.complementary {1, 2, 3, 8} {0, 5, 6} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a27 a109

theorem c14134 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 5, 9} → ¬ T {4, 6, 7} → False := by
  intro a209 n30 n105
  have hc := h.complementary {1, 2, 3, 8} {0, 5, 9} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 5, 9} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n30 (hc.mpr n105)

theorem c14139 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 6, 9} → T {4, 5, 7} → False := by
  intro a209 a33 a102
  have hc := h.complementary {1, 2, 3, 8} {0, 6, 9} a209 (by decide) (by decide)
  have he : ( {1, 2, 3, 8} : Finset Labels)ᶜ \ {0, 6, 9} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a33 a102

theorem c14159 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 6} → T {0, 5, 6} → T {0, 6, 7} → False := by
  intro a209 a23 a27 a31
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {0, 6} {4, 5, 7} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {0, 6} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 6} = {0, 5, 6} by decide)) a27)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 6} = {0, 6, 7} by decide)) a31)

theorem c14184 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 5} → ¬ T {4, 5, 6} → ¬ T {4, 5, 9} → False := by
  intro a209 n22 n101 n104
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 5} {0, 6, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n22 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 5} = {0, 4, 5} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 5} = {4, 5, 6} by decide)) ht)
  · exact n104 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 5} = {4, 5, 9} by decide)) ht)

theorem c14192 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 6} → ¬ T {4, 5, 6} → ¬ T {4, 6, 9} → False := by
  intro a209 n23 n101 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 6} {0, 5, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n101 (Eq.mp (congrArg T (show insert (5 : Labels) {4, 6} = {4, 5, 6} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c14194 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 6} → ¬ T {4, 6, 7} → ¬ T {4, 6, 9} → False := by
  intro a209 n23 n105 n107
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 6} {0, 7, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n23 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 6} = {0, 4, 6} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (7 : Labels) {4, 6} = {4, 6, 7} by decide)) ht)
  · exact n107 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 6} = {4, 6, 9} by decide)) ht)

theorem c14202 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → ¬ T {0, 4, 7} → ¬ T {4, 6, 7} → ¬ T {4, 7, 9} → False := by
  intro a209 n24 n105 n109
  obtain ⟨w, hw, ht⟩ := three_pos h {1, 2, 3, 8} {4, 7} {0, 6, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n24 (Eq.mp (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) ht)
  · exact n105 (Eq.mp (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) ht)
  · exact n109 (Eq.mp (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) ht)

theorem c14203 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  intro a209 a24 a105 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {4, 7} {0, 6, 9} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 7} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 7} = {4, 6, 7} by decide)) a105)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {4, 7} = {4, 7, 9} by decide)) a109)

theorem c14211 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 4, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  intro a209 a26 a107 a109
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {4, 9} {0, 6, 7} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {4, 9} = {0, 4, 9} by decide)) a26)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {4, 9} = {4, 6, 9} by decide)) a107)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {4, 9} = {4, 7, 9} by decide)) a109)

theorem c14257 (h : TenSystem T Q) :
    Q {1, 2, 3, 8} → T {0, 7, 9} → T {4, 7, 9} → T {6, 7, 9} → False := by
  intro a209 a35 a109 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 8} {7, 9} {0, 4, 6} a209 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (0 : Labels) {7, 9} = {0, 7, 9} by decide)) a35)
  · exact ht (Eq.mpr (congrArg T (show insert (4 : Labels) {7, 9} = {4, 7, 9} by decide)) a109)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {7, 9} = {6, 7, 9} by decide)) a118)

theorem c14262 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 5} → ¬ T {6, 7, 8} → False := by
  intro a210 n22 n117
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 5} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n22 (hc.mpr n117)

theorem c14264 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 6} → ¬ T {5, 7, 8} → False := by
  intro a210 n23 n114
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact n23 (hc.mpr n114)

theorem c14265 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {5, 7, 8} → False := by
  intro a210 a23 a114
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a23 a114

theorem c14266 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 4, 7} → ¬ T {5, 6, 8} → False := by
  intro a210 n24 n112
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n24 (hc.mpr n112)

theorem c14267 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 7} → T {5, 6, 8} → False := by
  intro a210 a24 a112
  have hc := h.complementary {1, 2, 3, 9} {0, 4, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 4, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a24 a112

theorem c14271 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 6} → T {4, 7, 8} → False := by
  intro a210 a27 a108
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 6} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 6} = {4, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a27 a108

theorem c14274 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 5, 8} → ¬ T {4, 6, 7} → False := by
  intro a210 n29 n105
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact n29 (hc.mpr n105)

theorem c14275 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 5, 8} → T {4, 6, 7} → False := by
  intro a210 a29 a105
  have hc := h.complementary {1, 2, 3, 9} {0, 5, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 5, 8} = {4, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a29 a105

theorem c14276 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 6, 7} → ¬ T {4, 5, 8} → False := by
  intro a210 n31 n103
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact n31 (hc.mpr n103)

theorem c14277 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 6, 7} → T {4, 5, 8} → False := by
  intro a210 a31 a103
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 7} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 7} = {4, 5, 8} := by decide
  rw [he] at hc
  exact hc.mp a31 a103

theorem c14279 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 6, 8} → T {4, 5, 7} → False := by
  intro a210 a32 a102
  have hc := h.complementary {1, 2, 3, 9} {0, 6, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 6, 8} = {4, 5, 7} := by decide
  rw [he] at hc
  exact hc.mp a32 a102

theorem c14280 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → ¬ T {0, 7, 8} → ¬ T {4, 5, 6} → False := by
  intro a210 n34 n101
  have hc := h.complementary {1, 2, 3, 9} {0, 7, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact n34 (hc.mpr n101)

theorem c14281 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 7, 8} → T {4, 5, 6} → False := by
  intro a210 a34 a101
  have hc := h.complementary {1, 2, 3, 9} {0, 7, 8} a210 (by decide) (by decide)
  have he : ( {1, 2, 3, 9} : Finset Labels)ᶜ \ {0, 7, 8} = {4, 5, 6} := by decide
  rw [he] at hc
  exact hc.mp a34 a101

theorem c14283 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 5} → T {0, 4, 6} → T {0, 4, 7} → False := by
  intro a210 a22 a23 a24
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 4} {5, 6, 7} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {0, 4} = {0, 4, 5} by decide)) a22)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)

theorem c14289 (h : TenSystem T Q) :
    Q {1, 2, 3, 9} → T {0, 4, 6} → T {0, 4, 7} → T {0, 4, 8} → False := by
  intro a210 a23 a24 a25
  obtain ⟨w, hw, ht⟩ := three_neg h {1, 2, 3, 9} {0, 4} {6, 7, 8} a210 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {0, 4} = {0, 4, 6} by decide)) a23)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {0, 4} = {0, 4, 7} by decide)) a24)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {0, 4} = {0, 4, 8} by decide)) a25)

end BorsukNine.FiniteObstruction

end OAI
