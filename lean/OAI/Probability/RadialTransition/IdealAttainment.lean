import OAI.Probability.RadialTransition.CoreConvergence

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma entropy_lower {d : ℝ} (hd : 0 ≤ d) : -1 ≤ d*Real.log d-d := by
  rcases eq_or_lt_of_le hd with rfl | hd
  · norm_num
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at hh
  have hm := mul_le_mul_of_nonneg_left hh hd.le
  rw [mul_sub, mul_inv_cancel₀ hd.ne', mul_one] at hm
  nlinarith

lemma grandPressure_continuous_h {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {B t β : ℝ} (hst : StableWith φ B) (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r:ℝ) → φ r ≤ 0) : Continuous (grandPressure φ t β) := by
  have hconv : ConvexOn ℝ univ (grandPressure φ t β) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hbb hab
    have hh := grandPressure_convex_mix hφ hb hst ht hc hβ hβ x y ha hbb hab
    have he : a*β+b*β = β := by nlinarith
    simpa only [he, smul_eq_mul] using hh
  exact continuousOn_univ.mp (hconv.continuousOn isOpen_univ)

lemma branch_le_density_value {Q : Pressure} {H : ℝ → ℝ} {β a h u d : ℝ}
    (hk : 0 ≤ β*a) (hd : Q β (h+β*a*u) = (h+β*a*u)*d-H d) :
    attractionBranch Q a u β h ≤ h*d-H d+β*a/2*d^2 := by
  unfold attractionBranch
  rw [hd]
  nlinarith [mul_nonneg hk (sq_nonneg (u-d))]

lemma branch_le_density_branch {Q : Pressure} {H : ℝ → ℝ} {β a h u d : ℝ}
    (hk : 0 ≤ β*a) (hd : Q β (h+β*a*u) = (h+β*a*u)*d-H d)
    (hdual : (h+β*a*d)*d-H d ≤ Q β (h+β*a*d)) :
    attractionBranch Q a u β h ≤ attractionBranch Q a d β h := by
  have hh := branch_le_density_value hk hd
  unfold attractionBranch at hh ⊢
  nlinarith [hdual]

lemma density_value_neg {H : ℝ → ℝ} {h k c B E U d : ℝ}
    (hκ : 0 < c-k/2) (hE : 0 ≤ E) (hU : 1 ≤ U)
    (hcut : h+B+E+1 ≤ (c-k/2)*U) (hd : U < d)
    (hH : c*d^2-B*d-E ≤ H d) : h*d-H d+k/2*d^2 < 0 := by
  have hd1 : 1 < d := hU.trans_lt hd
  have hkd : h+B+E+1 < (c-k/2)*d := hcut.trans_lt (mul_lt_mul_of_pos_left hd hκ)
  have hm := mul_lt_mul_of_pos_right hkd (show 0 < d by linarith)
  have he := mul_le_mul_of_nonneg_left (show 1 ≤ d by linarith) hE
  nlinarith

lemma ideal_density_cofinal {Q : Pressure} {H : ℝ → ℝ} {β a h c B E U : ℝ}
    (hk : 0 ≤ β*a) (hQ0 : 0 ≤ Q β h)
    (hmax : ∀ j, ∃ d ≥ 0, Q β j = j*d-H d)
    (hdual : ∀ j d, 0 ≤ d → j*d-H d ≤ Q β j)
    (hH : ∀ d, 0 ≤ d → c*d^2-B*d-E ≤ H d)
    (hκ : 0 < c-β*a/2) (hE : 0 ≤ E) (hU : 1 ≤ U)
    (hcut : h+B+E+1 ≤ (c-β*a/2)*U) (u : ℝ) :
    ∃ v ∈ Icc (0:ℝ) U, attractionBranch Q a u β h ≤ attractionBranch Q a v β h := by
  obtain ⟨d, hd, he⟩ := hmax (h+β*a*u)
  by_cases hdU : d ≤ U
  · exact ⟨d, ⟨hd, hdU⟩, branch_le_density_branch hk he (hdual _ d hd)⟩
  · refine ⟨0, ⟨le_rfl, by linarith⟩, ?_⟩
    have hneg := density_value_neg hκ hE hU hcut (lt_of_not_ge hdU) (hH d hd)
    have hh := branch_le_density_value hk he
    simp only [attractionBranch, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero]
    dsimp only [attractionBranch] at hh
    linarith

lemma ideal_exists_active_of_density_bound {Q : Pressure} {H : ℝ → ℝ} {β a h c B E U : ℝ}
    (hcont : Continuous (Q β)) (hk : 0 ≤ β*a) (hQ0 : 0 ≤ Q β h)
    (hmax : ∀ j, ∃ d ≥ 0, Q β j = j*d-H d)
    (hdual : ∀ j d, 0 ≤ d → j*d-H d ≤ Q β j)
    (hH : ∀ d, 0 ≤ d → c*d^2-B*d-E ≤ H d)
    (hκ : 0 < c-β*a/2) (hE : 0 ≤ E) (hU : 1 ≤ U)
    (hcut : h+B+E+1 ≤ (c-β*a/2)*U) :
    ∃ u ∈ Icc (0:ℝ) U, ActiveShift Q a β h u := by
  have hbr : Continuous (fun u => attractionBranch Q a u β h) := by
    unfold attractionBranch
    exact (hcont.comp (continuous_const.add (continuous_const.mul continuous_id))).sub
      (continuous_const.mul (continuous_id.pow 2))
  obtain ⟨u, hu, hmaxu⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (show 0 ≤ U by linarith)) hbr.continuousOn
  refine ⟨u, hu, fun v => ?_⟩
  obtain ⟨w, hw, hvw⟩ := ideal_density_cofinal hk hQ0 hmax hdual hH hκ hE hU hcut v
  exact hvw.trans (hmaxu hw)

lemma active_density_bound {Q : Pressure} {H : ℝ → ℝ} {β a h c B E U u : ℝ}
    (hk : 0 < β*a) (hQ0 : 0 ≤ Q β h)
    (hmax : ∀ j, ∃ d ≥ 0, Q β j = j*d-H d)
    (hdual : ∀ j d, 0 ≤ d → j*d-H d ≤ Q β j)
    (hH : ∀ d, 0 ≤ d → c*d^2-B*d-E ≤ H d)
    (hκ : 0 < c-β*a/2) (hE : 0 ≤ E) (hU : 1 ≤ U)
    (hcut : h+B+E+1 ≤ (c-β*a/2)*U) (hu : ActiveShift Q a β h u) : u ∈ Icc (0:ℝ) U := by
  obtain ⟨d, hd, he⟩ := hmax (h+β*a*u)
  have hh := hdual (h+β*a*d) d hd
  have hm := hu d
  dsimp only [attractionBranch] at hm
  rw [he] at hm
  have hsq : β*a*(u-d)^2 ≤ 0 := by nlinarith
  have hud : u = d := by
    have hs : (u-d)^2 ≤ 0 := le_of_mul_le_mul_left (by simpa only [mul_zero] using hsq) hk
    nlinarith [sq_nonneg (u-d)]
  subst u
  refine ⟨hd, ?_⟩
  by_contra! hdU
  have hneg := density_value_neg hκ hE hU hcut hdU (hH d hd)
  have hz := hu 0
  dsimp only [attractionBranch] at hz
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] at hz
  rw [he] at hz
  nlinarith

end RadialTransition
end

end OAI
