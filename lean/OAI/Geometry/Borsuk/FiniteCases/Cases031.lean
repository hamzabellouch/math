import Mathlib
import OAI.Geometry.Borsuk.TenLabels.Labels

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c6849 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 9} → T {5, 6, 8} → False := by
  intro a157 a49 a112
  have hc := h.complementary {0, 2, 4, 7} {1, 3, 9} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 8} := by decide
  rw [he] at hc
  exact hc.mp a49 a112

theorem c6850 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 5, 6} → ¬ T {3, 8, 9} → False := by
  intro a157 n55 n100
  have hc := h.complementary {0, 2, 4, 7} {1, 5, 6} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 5, 6} = {3, 8, 9} := by decide
  rw [he] at hc
  exact n55 (hc.mpr n100)

theorem c6852 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 5, 8} → ¬ T {3, 6, 9} → False := by
  intro a157 n57 n97
  have hc := h.complementary {0, 2, 4, 7} {1, 5, 8} a157 (by decide) (by decide)
  have he : ( {0, 2, 4, 7} : Finset Labels)ᶜ \ {1, 5, 8} = {3, 6, 9} := by decide
  rw [he] at hc
  exact n57 (hc.mpr n97)

theorem c6865 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 5} → T {1, 3, 6} → T {1, 3, 9} → False := by
  intro a157 a45 a46 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {1, 3} {5, 6, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 3} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c6897 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 9} → T {1, 5, 9} → T {1, 8, 9} → False := by
  intro a157 a49 a58 a64
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {1, 9} {3, 5, 8} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {1, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 9} = {1, 8, 9} by decide)) a64)

theorem c6902 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 3, 5} → ¬ T {3, 5, 6} → ¬ T {3, 5, 8} → False := by
  intro a157 n45 n91 n93
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {3, 5} {1, 6, 8} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n45 (Eq.mp (congrArg T (show insert (1 : Labels) {3, 5} = {1, 3, 5} by decide)) ht)
  · exact n91 (Eq.mp (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) ht)

theorem c6909 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {3, 5, 6} → T {3, 5, 8} → T {3, 5, 9} → False := by
  intro a157 a91 a93 a94
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {3, 5} {6, 8, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {3, 5} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 5} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {3, 5} = {3, 5, 9} by decide)) a94)

theorem c6929 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 3, 9} → T {3, 5, 9} → T {3, 8, 9} → False := by
  intro a157 a49 a94 a100
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {3, 9} {1, 5, 8} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {3, 9} = {1, 3, 9} by decide)) a49)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 9} = {3, 8, 9} by decide)) a100)

theorem c6935 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 8} → False := by
  intro a157 a55 a91 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {5, 6} {1, 3, 8} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {5, 6} = {5, 6, 8} by decide)) a112)

theorem c6942 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 5, 8} → ¬ T {3, 5, 8} → ¬ T {5, 6, 8} → False := by
  intro a157 n57 n93 n112
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {5, 8} {1, 3, 6} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n93 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)

theorem c6947 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 5, 8} → T {5, 6, 8} → T {5, 8, 9} → False := by
  intro a157 a57 a112 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {5, 8} {1, 6, 9} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 8} = {5, 8, 9} by decide)) a116)

theorem c6974 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → False := by
  intro a157 n64 n100 n116
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {8, 9} {1, 3, 5} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)

theorem c6975 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → T {1, 8, 9} → T {3, 8, 9} → T {5, 8, 9} → False := by
  intro a157 a64 a100 a116
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 7} {8, 9} {1, 3, 5} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) a64)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) a100)
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) a116)

theorem c6976 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {1, 8, 9} → ¬ T {3, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a157 n64 n100 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {8, 9} {1, 3, 6} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n64 (Eq.mp (congrArg T (show insert (1 : Labels) {8, 9} = {1, 8, 9} by decide)) ht)
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c6980 (h : TenSystem T Q) :
    Q {0, 2, 4, 7} → ¬ T {3, 8, 9} → ¬ T {5, 8, 9} → ¬ T {6, 8, 9} → False := by
  intro a157 n100 n116 n119
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 7} {8, 9} {3, 5, 6} a157 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n100 (Eq.mp (congrArg T (show insert (3 : Labels) {8, 9} = {3, 8, 9} by decide)) ht)
  · exact n116 (Eq.mp (congrArg T (show insert (5 : Labels) {8, 9} = {5, 8, 9} by decide)) ht)
  · exact n119 (Eq.mp (congrArg T (show insert (6 : Labels) {8, 9} = {6, 8, 9} by decide)) ht)

theorem c6985 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 3, 6} → T {5, 7, 9} → False := by
  intro a158 a46 a115
  have hc := h.complementary {0, 2, 4, 8} {1, 3, 6} a158 (by decide) (by decide)
  have he : ( {0, 2, 4, 8} : Finset Labels)ᶜ \ {1, 3, 6} = {5, 7, 9} := by decide
  rw [he] at hc
  exact hc.mp a46 a115

theorem c6988 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 3, 9} → ¬ T {5, 6, 7} → False := by
  intro a158 n49 n111
  have hc := h.complementary {0, 2, 4, 8} {1, 3, 9} a158 (by decide) (by decide)
  have he : ( {0, 2, 4, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact n49 (hc.mpr n111)

theorem c6989 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 3, 9} → T {5, 6, 7} → False := by
  intro a158 a49 a111
  have hc := h.complementary {0, 2, 4, 8} {1, 3, 9} a158 (by decide) (by decide)
  have he : ( {0, 2, 4, 8} : Finset Labels)ᶜ \ {1, 3, 9} = {5, 6, 7} := by decide
  rw [he] at hc
  exact hc.mp a49 a111

theorem c7009 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 3, 6} → T {1, 3, 7} → T {1, 3, 9} → False := by
  intro a158 a46 a47 a49
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {1, 3} {6, 7, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 3} = {1, 3, 6} by decide)) a46)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 3} = {1, 3, 7} by decide)) a47)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {1, 3} = {1, 3, 9} by decide)) a49)

theorem c7075 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 7} → False := by
  intro a158 a55 a91 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c7081 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {3, 5, 6} → T {5, 6, 7} → T {5, 6, 9} → False := by
  intro a158 a91 a111 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 6} {3, 7, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 6} = {5, 6, 9} by decide)) a113)

theorem c7082 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 5, 7} → ¬ T {3, 5, 7} → ¬ T {5, 6, 7} → False := by
  intro a158 n56 n92 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 8} {5, 7} {1, 3, 6} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n56 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 7} = {1, 5, 7} by decide)) ht)
  · exact n92 (Eq.mp (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) ht)

theorem c7089 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {3, 5, 7} → T {5, 6, 7} → T {5, 7, 9} → False := by
  intro a158 a92 a111 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 7} {3, 6, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 7} = {3, 5, 7} by decide)) a92)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 7} = {5, 6, 7} by decide)) a111)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {5, 7} = {5, 7, 9} by decide)) a115)

theorem c7091 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 9} → T {3, 5, 9} → T {5, 6, 9} → False := by
  intro a158 a58 a94 a113
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 9} {1, 3, 6} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 9} = {5, 6, 9} by decide)) a113)

theorem c7093 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 5, 9} → T {3, 5, 9} → T {5, 7, 9} → False := by
  intro a158 a58 a94 a115
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {5, 9} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 9} = {1, 5, 9} by decide)) a58)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 9} = {3, 5, 9} by decide)) a94)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 9} = {5, 7, 9} by decide)) a115)

theorem c7098 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a158 n59 n95 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 8} {6, 7} {1, 3, 5} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

theorem c7101 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 6, 7} → T {3, 6, 7} → T {6, 7, 9} → False := by
  intro a158 a59 a95 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {6, 7} {1, 3, 9} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (9 : Labels) {6, 7} = {6, 7, 9} by decide)) a118)

theorem c7109 (h : TenSystem T Q) :
    Q {0, 2, 4, 8} → T {1, 6, 9} → T {3, 6, 9} → T {6, 7, 9} → False := by
  intro a158 a61 a97 a118
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 8} {6, 9} {1, 3, 7} a158 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 9} = {1, 6, 9} by decide)) a61)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 9} = {3, 6, 9} by decide)) a97)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {6, 9} = {6, 7, 9} by decide)) a118)

theorem c7122 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 3, 5} → ¬ T {6, 7, 8} → False := by
  intro a159 n45 n117
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 5} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact n45 (hc.mpr n117)

theorem c7123 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {6, 7, 8} → False := by
  intro a159 a45 a117
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 5} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 5} = {6, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a45 a117

theorem c7125 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 6} → T {5, 7, 8} → False := by
  intro a159 a46 a114
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 6} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 6} = {5, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a46 a114

theorem c7126 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 3, 7} → ¬ T {5, 6, 8} → False := by
  intro a159 n47 n112
  have hc := h.complementary {0, 2, 4, 9} {1, 3, 7} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 3, 7} = {5, 6, 8} := by decide
  rw [he] at hc
  exact n47 (hc.mpr n112)

theorem c7131 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 5, 6} → T {3, 7, 8} → False := by
  intro a159 a55 a98
  have hc := h.complementary {0, 2, 4, 9} {1, 5, 6} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 5, 6} = {3, 7, 8} := by decide
  rw [he] at hc
  exact hc.mp a55 a98

theorem c7132 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 5, 7} → ¬ T {3, 6, 8} → False := by
  intro a159 n56 n96
  have hc := h.complementary {0, 2, 4, 9} {1, 5, 7} a159 (by decide) (by decide)
  have he : ( {0, 2, 4, 9} : Finset Labels)ᶜ \ {1, 5, 7} = {3, 6, 8} := by decide
  rw [he] at hc
  exact n56 (hc.mpr n96)

theorem c7151 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {1, 5, 6} → T {1, 5, 7} → False := by
  intro a159 a45 a55 a56
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {1, 5} {3, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {1, 5} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)

theorem c7155 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 3, 5} → T {1, 5, 7} → T {1, 5, 8} → False := by
  intro a159 a45 a56 a57
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {1, 5} {3, 7, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {1, 5} = {1, 3, 5} by decide)) a45)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {1, 5} = {1, 5, 7} by decide)) a56)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {1, 5} = {1, 5, 8} by decide)) a57)

theorem c7197 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {3, 5, 6} → T {3, 6, 7} → T {3, 6, 8} → False := by
  intro a159 a91 a95 a96
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {3, 6} {5, 7, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (5 : Labels) {3, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {3, 6} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {3, 6} = {3, 6, 8} by decide)) a96)

theorem c7215 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 5, 6} → T {3, 5, 6} → T {5, 6, 7} → False := by
  intro a159 a55 a91 a111
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {5, 6} {1, 3, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 6} = {1, 5, 6} by decide)) a55)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 6} = {3, 5, 6} by decide)) a91)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 6} = {5, 6, 7} by decide)) a111)

theorem c7231 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 5, 8} → T {3, 5, 8} → T {5, 6, 8} → False := by
  intro a159 a57 a93 a112
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {5, 8} {1, 3, 6} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) a57)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)

theorem c7234 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 5, 8} → ¬ T {5, 6, 8} → ¬ T {5, 7, 8} → False := by
  intro a159 n57 n112 n114
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {5, 8} {1, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n57 (Eq.mp (congrArg T (show insert (1 : Labels) {5, 8} = {1, 5, 8} by decide)) ht)
  · exact n112 (Eq.mp (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) ht)
  · exact n114 (Eq.mp (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) ht)

theorem c7237 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {3, 5, 8} → T {5, 6, 8} → T {5, 7, 8} → False := by
  intro a159 a93 a112 a114
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {5, 8} {3, 6, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {5, 8} = {3, 5, 8} by decide)) a93)
  · exact ht (Eq.mpr (congrArg T (show insert (6 : Labels) {5, 8} = {5, 6, 8} by decide)) a112)
  · exact ht (Eq.mpr (congrArg T (show insert (7 : Labels) {5, 8} = {5, 7, 8} by decide)) a114)

theorem c7238 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 7} → ¬ T {3, 6, 7} → ¬ T {5, 6, 7} → False := by
  intro a159 n59 n95 n111
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 7} {1, 3, 5} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n95 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)

theorem c7241 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → T {1, 6, 7} → T {3, 6, 7} → T {6, 7, 8} → False := by
  intro a159 a59 a95 a117
  obtain ⟨w, hw, ht⟩ := three_neg h {0, 2, 4, 9} {6, 7} {1, 3, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact ht (Eq.mpr (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) a59)
  · exact ht (Eq.mpr (congrArg T (show insert (3 : Labels) {6, 7} = {3, 6, 7} by decide)) a95)
  · exact ht (Eq.mpr (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) a117)

theorem c7242 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 7} → ¬ T {5, 6, 7} → ¬ T {6, 7, 8} → False := by
  intro a159 n59 n111 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 7} {1, 5, 8} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n59 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 7} = {1, 6, 7} by decide)) ht)
  · exact n111 (Eq.mp (congrArg T (show insert (5 : Labels) {6, 7} = {5, 6, 7} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (8 : Labels) {6, 7} = {6, 7, 8} by decide)) ht)

theorem c7248 (h : TenSystem T Q) :
    Q {0, 2, 4, 9} → ¬ T {1, 6, 8} → ¬ T {3, 6, 8} → ¬ T {6, 7, 8} → False := by
  intro a159 n60 n96 n117
  obtain ⟨w, hw, ht⟩ := three_pos h {0, 2, 4, 9} {6, 8} {1, 3, 7} a159 (by decide) (by decide) (by decide) (by decide)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl
  · exact n60 (Eq.mp (congrArg T (show insert (1 : Labels) {6, 8} = {1, 6, 8} by decide)) ht)
  · exact n96 (Eq.mp (congrArg T (show insert (3 : Labels) {6, 8} = {3, 6, 8} by decide)) ht)
  · exact n117 (Eq.mp (congrArg T (show insert (7 : Labels) {6, 8} = {6, 7, 8} by decide)) ht)

end BorsukNine.FiniteObstruction

end OAI
