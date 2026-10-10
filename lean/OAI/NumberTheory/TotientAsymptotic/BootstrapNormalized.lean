import OAI.NumberTheory.TotientAsymptotic.BootstrapIndex

namespace OAI

/-! Normalize the pointwise bootstrap by the logarithmic counting scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma bootstrap_small_term : ∀ᶠ J : ℕ in atTop,
    (((2:ℝ)^J)^(3/4:ℝ))*(J:ℝ)/(2:ℝ)^J ≤ 1 := by
  have hl : 0 < Real.log (2:ℝ)/4 := by positivity
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (Real.log 2/4) hl).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with J hJ
  have he : (((2:ℝ)^J)^(3/4:ℝ))*(J:ℝ)/(2:ℝ)^J =
      (J:ℝ)*Real.exp (-(Real.log 2/4)*(J:ℝ)) := by
    have hp : (2:ℝ)^J = Real.exp ((J:ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [hp,Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    rw [div_eq_mul_inv,← Real.exp_neg]
    calc
      _ = (J:ℝ)*(Real.exp (((J:ℝ)*Real.log 2)*(3/4:ℝ))*Real.exp (-((J:ℝ)*Real.log 2))) := by ring
      _ = _ := by
        rw [← Real.exp_add]
        apply congrArg (fun t : ℝ => (J:ℝ)*Real.exp t)
        ring
  rw [he]
  simpa only [Function.comp_apply,Real.rpow_one] using hJ.le

 theorem bootstrap_normalized : ∃ A : ℝ,0 < A ∧ ∃ δ : ℕ → ℝ,
    Tendsto δ atTop (nhds 0) ∧ ∀ᶠ J : ℕ in atTop,
    1 ≤ bootstrapIndex J ∧ bootstrapIndex J < J ∧
    V ((2:ℝ)^J)*(J:ℝ)/(2:ℝ)^J ≤ 1+δ J*dyadicTotientEnvelope J+
      A*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
  obtain ⟨C,hC,ε,hε,hpoint⟩ := bootstrap_pointwise
  let δ := fun J => ε J/Real.log 2
  have hδ : Tendsto δ atTop (nhds 0) := by
    simpa only [zero_div] using hε.div_const (Real.log 2)
  refine ⟨C/Real.log 2,by positivity,δ,hδ,?_⟩
  filter_upwards [hpoint,bootstrap_index_bounds,bootstrap_small_term,eventually_ge_atTop (2:ℕ)] with J hp hidx hs hJ
  obtain ⟨hK,hKJ,hlogK,hsize⟩ := hidx
  refine ⟨hK,hKJ,?_⟩
  let x := (2:ℝ)^J
  have hx0 : 0 < x := by positivity
  have hJ0 : (0:ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlog2 : 0 < Real.log (2:ℝ) := by positivity
  have hlog : Real.log x = (J:ℝ)*Real.log 2 := Real.log_pow _ _
  have hxlog : 0 < Real.log x := by rw [hlog]; positivity
  have hb : B x ≤ Real.log J := by
    unfold B
    rw [hlog,Real.log_mul hJ0.ne' hlog2.ne']
    have hh : Real.log (Real.log (2:ℝ)) ≤ 0 := Real.log_nonpos hlog2.le (by linarith [Real.log_two_lt_d9])
    linarith
  have hB0 : 0 ≤ B x := by
    have hj2 : (2:ℝ) ≤ J := by exact_mod_cast hJ
    have hl : 1 ≤ Real.log x := by rw [hlog]; nlinarith [Real.log_two_gt_d9]
    exact Real.log_nonneg hl
  have hlj : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
  have hKlog : 1+Real.log (bootstrapIndex J:ℝ) ≤ 1+Real.log J := by
    have hh : Real.log (bootstrapIndex J:ℝ) ≤ Real.log (J:ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < bootstrapIndex J by omega))
        (by exact_mod_cast hKJ.le)
    linarith
  have hh := mul_le_mul_of_nonneg_right (hp (bootstrapIndex J) hK hsize) (div_nonneg hJ0.le hx0.le)
  have hmain :
      C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
        (1+Real.log (bootstrapIndex J))*(J:ℝ)/x ≤
      (C/Real.log 2)*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
    have hid : C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
        (1+Real.log (bootstrapIndex J))*(J:ℝ)/x =
        (C/Real.log 2)*((1+B x)*(1+Real.log (bootstrapIndex J)))*dyadicTotientEnvelope (bootstrapIndex J) := by
      rw [hlog]
      field_simp
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (dyadicTotientEnvelope_one_le _))
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [pow_two] using (mul_le_mul (by linarith : 1+B x ≤ 1+Real.log J) hKlog
      (by have := Real.log_nonneg (show (1:ℝ) ≤ bootstrapIndex J by exact_mod_cast hK); linarith)
      (by linarith))
  have herr : ε J*(dyadicTotientEnvelope J*x/Real.log x)*(J:ℝ)/x=δ J*dyadicTotientEnvelope J := by
    dsimp [δ]
    rw [hlog]
    field_simp
  have hout : V x*(J:ℝ)/x ≤ x^(3/4:ℝ)*(J:ℝ)/x+
      δ J*dyadicTotientEnvelope J+
      (C/Real.log 2)*(1+Real.log J)^2*dyadicTotientEnvelope (bootstrapIndex J) := by
    calc
      _ ≤ (x^(3/4:ℝ)+ε J*(dyadicTotientEnvelope J*x/Real.log x)+
          C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
            (1+Real.log (bootstrapIndex J)))*((J:ℝ)/x) := by simpa only [mul_div_assoc] using hh
      _ = x^(3/4:ℝ)*(J:ℝ)/x+δ J*dyadicTotientEnvelope J+
          C*(x/Real.log x)*(1+B x)*dyadicTotientEnvelope (bootstrapIndex J)*
            (1+Real.log (bootstrapIndex J))*(J:ℝ)/x := by rw [add_mul,add_mul]; rw [← herr]; ring
      _ ≤ _ := add_le_add le_rfl hmain
  exact hout.trans (add_le_add (add_le_add hs le_rfl) le_rfl)

end TotientAsymptotic

end

end OAI
