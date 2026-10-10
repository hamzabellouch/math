import OAI.NumberTheory.TotientAsymptotic.ValueOmega
import OAI.NumberTheory.TotientAsymptotic.TupleCoefficient
import OAI.NumberTheory.TotientAsymptotic.AllCollisionCount

namespace OAI

noncomputable section
open scoped BigOperators Topology Classical
open Filter

namespace TotientAsymptotic

def smallValues (x : ℝ) : Finset ℕ := Finset.Icc 1 ⌊x^(19/20 : ℝ)⌋₊

lemma small_value_count {x : ℝ} (hx : 0 ≤ x) : ((smallValues x).card : ℝ) ≤ x^(19/20 : ℝ) := by
  have he : (smallValues x).card=⌊x^(19/20 : ℝ)⌋₊ := by simp [smallValues,Nat.card_Icc]
  rw [he]
  exact Nat.floor_le (Real.rpow_nonneg hx _)

lemma small_values_negligible (hren : FordRenewalInput) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ((smallValues x).card : ℝ) ≤ ε*tupleNormalization x := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ)<1/20 by norm_num)).tendsto_div_nhds_zero
  filter_upwards [ht.eventually (eventually_lt_nhds hε),G_eventually_one_le hren,
    eventually_gt_atTop (1 : ℝ)] with x hs hG hx
  have hx0 := zero_lt_one.trans hx
  have hlog := Real.log_pos hx
  have hpow : (0 : ℝ)<x^(1/20 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hh := (div_le_iff₀ hpow).mp hs.le
  have he : x^(19/20 : ℝ)*x^(1/20 : ℝ)=x := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hsmall : x^(19/20 : ℝ) ≤ ε*(x/Real.log x) := by
    have hmul : x^(19/20 : ℝ)*Real.log x ≤ ε*x := by
      calc
        _ ≤ x^(19/20 : ℝ)*(ε*x^(1/20 : ℝ)) :=
          mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx0.le _)
        _ = ε*(x^(19/20 : ℝ)*x^(1/20 : ℝ)) := by ring
        _ = _ := by rw [he]
    simpa only [mul_div_assoc] using (le_div_iff₀ hlog).mpr hmul
  exact (small_value_count hx0.le).trans (hsmall.trans (by
    unfold tupleNormalization
    have ha : 0 ≤ ε*(x/Real.log x) := by positivity
    simpa only [mul_assoc] using le_mul_of_one_le_right ha hG))

lemma omega_values_negligible (hmertens : MertensProductInput) (hren : FordRenewalInput)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ x : ℝ in atTop, ((largeOmegaValues x).card : ℝ) ≤ ε*tupleNormalization x := by
  obtain ⟨C,hC,hcount⟩ := large_omega_value_count hmertens
  have ht : Tendsto (fun x : ℝ => C/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [hcount,ht.eventually (eventually_lt_nhds hε),G_eventually_one_le hren,
    eventually_gt_atTop (1 : ℝ)] with x hc he hG hx
  have hx0 := zero_lt_one.trans hx
  have hlog := Real.log_pos hx
  have hscale : 0 ≤ x/Real.log x := by positivity
  apply hc.trans
  apply (mul_le_mul_of_nonneg_right he.le hscale).trans
  unfold tupleNormalization
  simpa only [mul_assoc] using le_mul_of_one_le_right (mul_nonneg hε.le hscale) hG

end TotientAsymptotic

end

end OAI
