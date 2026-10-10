import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedRootFlagErrorNumerics

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedRootFlagError
open Construction Conclusion Filter

theorem selected_root_error_rate_eventually (Bs BD Bz F D H : ℝ)
    (hF : 0≤F) (hH : 0≤H) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀a : ℝ,(3/2000:ℝ)≤a → ∀l≤k,
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp (a*L)) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp (a*L)) ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_root_flag_error_eventually Bs BD Bz F D H hF hH hk,
    eventually_ge_atTop (0:ℝ)] with L he hL
  intro a ha l hl
  have hd : Real.exp (-Real.exp (a*L))≤Real.exp (-Real.exp ((3/2000:ℝ)*L)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hL)))
  have hp := mul_le_mul_of_nonneg_left hd (show 0≤
    (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
      Real.exp (D*(L+1)^2) by positivity)
  exact ⟨hp.trans (he l hl).1,hp.trans (he l hl).2⟩

theorem selected_root_collision_error_eventually (Bs BD Bz F D H : ℝ)
    (hF : 0≤F) (hH : 0≤H) {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀l≤k,
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤
          Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      (Fintype.card (AllowedFrequency (frequencyBound Bs BD Bz k L) l):ℝ)*F*
        Real.exp (D*(L+1)^2)*Real.exp (-Real.exp ((1/500:ℝ)*L)) ≤
          Real.exp (-H*(bulkSize k L:ℝ)) := by
  filter_upwards [selected_root_error_rate_eventually Bs BD Bz F D H hF hH hk] with L he
  exact he (1/500) (by norm_num)

end Ostmann.Arithmetic.HistorySelectedRootFlagError

end

end OAI
