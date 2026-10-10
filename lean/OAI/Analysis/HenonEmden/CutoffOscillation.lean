import OAI.Analysis.HenonEmden.Cutoff

namespace OAI

universe uE

section CutoffOscillation

open Set Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

variable {E : Type uE} [NormedAddCommGroup E]

lemma d_nonneg (x : E) : 0 ≤ d x := gapProfile_nonneg _
lemma d_le_one (x : E) : d x ≤ 1 := gapProfile_le_one _
lemma d_pos_iff (x : E) : 0 < d x ↔ ‖x‖ < 2 := by
  simp only [d,gapProfile,lt_min_iff,lt_max_iff,lt_self_iff_false,or_false]
  constructor
  · intro h; linarith [h.2]
  · intro h; constructor <;> linarith

lemma d_oscillation (x y : E) : |d x-d y| ≤ dist x y := by
  exact (gapProfile_oscillation ‖x‖ ‖y‖).trans (by simpa only [dist_eq_norm] using abs_norm_sub_norm_le x y)

lemma pow_d_le_self (x : E) {j : ℕ} (hj : 1 ≤ j) : (d x)^j ≤ d x := by
  simpa only [pow_one] using pow_le_pow_of_le_one (d_nonneg x) (d_le_one x) hj

lemma close_gap_comparable {x y : E} {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1/2)
    {j : ℕ} (hj : 1 ≤ j) (hxy : dist x y ≤ δ*(d x)^j) :
    d x/2 ≤ d y ∧ d y ≤ 2*d x := by
  have hdist : dist x y ≤ δ*d x := hxy.trans (mul_le_mul_of_nonneg_left (pow_d_le_self x hj) hδ)
  have hg := abs_le.mp (d_oscillation x y)
  have hd := d_nonneg x
  constructor <;> nlinarith

lemma norm_segment_gap {x y : E} {D : ℝ} (hD : d x+dist x y ≤ D)
    {t : ℝ} (ht : t ∈ uIcc ‖x‖ ‖y‖) : 0 ≤ t ∧ gapProfile t ≤ D := by
  refine ⟨le_trans (le_min (norm_nonneg _) (norm_nonneg _)) ht.1,?_⟩
  have hdist : |t-‖x‖| ≤ |‖y‖-‖x‖| := by
    exact (abs_sub_le_iff.mpr ⟨by
      have hmax : max ‖x‖ ‖y‖ ≤ ‖x‖+|‖y‖-‖x‖| := by
        apply max_le
        · linarith [abs_nonneg (‖y‖-‖x‖)]
        · linarith [le_abs_self (‖y‖-‖x‖)]
      linarith [ht.2]
    ,by
      have hmin : ‖x‖-|‖y‖-‖x‖| ≤ min ‖x‖ ‖y‖ := by
        apply le_min
        · linarith [abs_nonneg (‖y‖-‖x‖)]
        · linarith [neg_abs_le (‖y‖-‖x‖)]
      linarith [ht.1]⟩)
  have hn : |‖y‖-‖x‖| ≤ dist x y := by
    simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
  have hg := (abs_le.mp (gapProfile_oscillation t ‖x‖)).2
  change gapProfile t ≤ D
  change gapProfile ‖x‖+dist x y ≤ D at hD
  linarith

variable [InnerProductSpace ℝ E]
lemma w_oscillation {n : ℕ} (hn : 1 ≤ n) {x y : E} {D : ℝ} (hD : 0 ≤ D)
    (hxy : d x+dist x y ≤ D) :
    |w n y-w n x| ≤ wDerivativeConstant n*D^(N n-2)*dist x y := by
  rw [w_eq_profile,w_eq_profile]
  have hh := wProfile_oscillation hn hD (fun _ ht => norm_segment_gap hxy ht)
  have hn' : |‖y‖-‖x‖| ≤ dist x y := by
    simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x
  exact hh.trans (mul_le_mul_of_nonneg_left hn' (mul_nonneg (constants_nonneg n).2.2 (pow_nonneg hD _)))

end HenonLaneEmden.Cutoff
end
end CutoffOscillation

end OAI
