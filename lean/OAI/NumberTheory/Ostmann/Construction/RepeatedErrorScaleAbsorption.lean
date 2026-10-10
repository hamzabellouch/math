import OAI.NumberTheory.Ostmann.Construction.RepeatedErrorScaleCombinatorial

namespace OAI

noncomputable section
namespace Ostmann.Construction.RepeatedErrorScale
open Filter

theorem absorption_eventually {K Bs : ℝ} (_hK : 0≤K) (hBs : 200≤Bs)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,
      K * Real.exp (-(Conclusion.initialGap Bs k L-(14+6*(k:ℝ)))/2) *
        (5000/L)^(2*Conclusion.bulkSize k L) * Real.exp (24*(Conclusion.bulkSize k L:ℝ)) *
        (tupleSize k L:ℝ)^(tupleSize k L) * Real.exp (2*L) ≤
      (1/2)*Real.exp (-27*(Conclusion.bulkSize k L:ℝ)) := by
  have hm := Conclusion.bulkSize_tendsto_atTop hk
  have hfixed := (Real.tendsto_exp_atTop.comp hm).eventually_ge_atTop
    (K*Real.exp ((14+6*(k:ℝ))/2))
  filter_upwards [combinatorial_bound_eventually hk,hfixed,
    hm.eventually_ge_atTop 1,eventually_ge_atTop (4:ℝ)] with L hcomb hfixed hm1 hL
  let m := Conclusion.bulkSize k L
  have hm0 : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hz : 1≤Conclusion.bulkScale k := by
    unfold Conclusion.bulkScale
    exact one_le_pow₀ (by exact_mod_cast (show 1≤k by omega))
  have hlog : 0≤Real.log (Conclusion.bulkScale k) := Real.log_nonneg hz
  have hfloor := (Conclusion.bulkSize_bounds k (show 0≤L by linarith)).1
  have hLm : L≤2*(m:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hz (show 0≤L by linarith)
    change Conclusion.bulkScale k*L-2<(m:ℝ) at hfloor
    nlinarith
  have hsplit : Real.exp (-(Conclusion.initialGap Bs k L-(14+6*(k:ℝ)))/2)=
      Real.exp ((14+6*(k:ℝ))/2)*Real.exp (-Conclusion.initialGap Bs k L/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (K*Real.exp ((14+6*(k:ℝ))/2))*Real.exp (-Conclusion.initialGap Bs k L/2) *
        ((5000/L)^(2*m)*(tupleSize k L:ℝ)^(tupleSize k L)) *
        Real.exp (24*(m:ℝ))*Real.exp (2*L) := by rw [hsplit]; ring
    _ ≤ Real.exp (m:ℝ)*Real.exp (-Conclusion.initialGap Bs k L/2) *
        Real.exp ((29+2*Real.log (Conclusion.bulkScale k))*(m:ℝ)) *
        Real.exp (24*(m:ℝ))*Real.exp (4*(m:ℝ)) := by
      have hexpL : Real.exp (2*L)≤Real.exp (4*(m:ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      change K*Real.exp ((14+6*(k:ℝ))/2)≤Real.exp (m:ℝ) at hfixed
      gcongr
    _ ≤ Real.exp (-28*(m:ℝ)) := by
      repeat rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      unfold Conclusion.initialGap
      dsimp only [m] at hm0 ⊢
      nlinarith [mul_le_mul_of_nonneg_right hBs hm0,mul_nonneg hlog hm0]
    _ ≤ _ := by
      have he : Real.exp (-(m:ℝ))≤(1/2:ℝ) := by
        have htwo : (2:ℝ)≤Real.exp (m:ℝ) := by
          have h := Real.add_one_le_exp (m:ℝ)
          change 1≤(m:ℝ) at hm1
          linarith
        simpa only [one_div,← Real.exp_neg] using
          one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) htwo
      have heq : Real.exp (-28*(m:ℝ))=Real.exp (-(m:ℝ))*Real.exp (-27*(m:ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le

end Ostmann.Construction.RepeatedErrorScale

end

end OAI
