import OAI.NumberTheory.Ostmann.Conclusion.Scales

namespace OAI

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped Topology

def levelZeroSupportWidth (k : ℕ) : ℝ := 14+6*(k:ℝ)

theorem initialGap_nonneg (Bs : ℝ) (hBs : 0≤Bs) {k : ℕ} (hk : 0 < k) (L : ℝ) :
    0≤Conclusion.initialGap Bs k L := by
  have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
  have hscale : 1≤Conclusion.bulkScale k := by
    unfold Conclusion.bulkScale
    exact one_le_pow₀ hk1
  have hlog := Real.log_nonneg hscale
  unfold Conclusion.initialGap
  positivity

theorem eventually_levelZero_sqrt_reserve {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop,
      levelZeroSupportWidth k+Real.log 2≤Real.sqrt (Conclusion.bulkSize k L) :=
  (Real.tendsto_sqrt_atTop.comp (Conclusion.bulkSize_tendsto_atTop hk)).eventually_ge_atTop _

theorem eventually_levelZero_period_frequency (Bs BD Bz : ℝ) (hBs : 0≤Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ M X : ℝ, 0 < M → 0 < X →
      Real.log M≤Real.log X+Conclusion.initialGap Bs k L+levelZeroSupportWidth k →
      M/(4*X)≤(Conclusion.frequencyBound Bs BD Bz k L 0:ℝ) := by
  filter_upwards [eventually_levelZero_sqrt_reserve hk] with L hreserve
  intro M X hM hX hs
  have hgap := initialGap_nonneg Bs hBs hk L
  have hwidth : 0≤levelZeroSupportWidth k := by unfold levelZeroSupportWidth; positivity
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hbudget : Conclusion.frequencyBudget Bs BD Bz k L 0=
      Conclusion.initialGap Bs k L+Real.sqrt (Conclusion.bulkSize k L) := by
    simp [Conclusion.frequencyBudget]
  have htwo : (2:ℝ)≤Real.exp (Conclusion.frequencyBudget Bs BD Bz k L 0) := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [hbudget]; linarith)
  have hfloor := Nat.lt_floor_add_one (Real.exp (Conclusion.frequencyBudget Bs BD Bz k L 0))
  change Real.exp (Conclusion.frequencyBudget Bs BD Bz k L 0)<
    (Conclusion.frequencyBound Bs BD Bz k L 0:ℝ)+1 at hfloor
  have hhalf : Real.exp (Conclusion.frequencyBudget Bs BD Bz k L 0)/2≤
      (Conclusion.frequencyBound Bs BD Bz k L 0:ℝ) := by linarith
  have hlogbound : Real.log M≤Real.log X+Conclusion.frequencyBudget Bs BD Bz k L 0 := by
    rw [hbudget]
    linarith
  have hexp := Real.exp_le_exp.mpr hlogbound
  rw [Real.exp_add,Real.exp_log hM,Real.exp_log hX] at hexp
  apply le_trans _ hhalf
  apply (div_le_iff₀ (by positivity : 0<4*X)).mpr
  nlinarith [Real.exp_pos (Conclusion.frequencyBudget Bs BD Bz k L 0)]

theorem eventually_levelZero_nat_period_frequency (Bs BD Bz : ℝ) (hBs : 0≤Bs)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, ∀ X : ℝ, 0 < X →
      Real.log (M:ℝ)≤Real.log X+Conclusion.initialGap Bs k L+levelZeroSupportWidth k →
      (M:ℝ)/(4*X)≤(Conclusion.frequencyBound Bs BD Bz k L 0:ℝ) := by
  filter_upwards [eventually_levelZero_period_frequency Bs BD Bz hBs hk] with L hL
  intro M X hX hs
  by_cases hM : M=0
  · simp [hM]
  · exact hL M X (by exact_mod_cast Nat.pos_of_ne_zero hM) hX hs

end Ostmann.Construction

end

end OAI
