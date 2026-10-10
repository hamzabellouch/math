import OAI.NumberTheory.TotientAsymptotic.FordDimensionScale

namespace OAI

/-! Values below the three-quarter power are negligible at every Ford dimension. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma small_value_gaussian_scale : ∀ᶠ x : ℝ in atTop,
    x^(3/4:ℝ) ≤ (x/Real.log x)*Real.exp (-(m x:ℝ)^2/4) := by
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) 1 (by norm_num)
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) 1 (by norm_num)
  have hlim := ((h2.add h1).const_mul 4).comp B_tendsto
  simp only [add_zero,mul_zero] at hlim
  filter_upwards [dimension_exponential_lower,eventually_gt_atTop (1:ℝ),
    B_tendsto.eventually (eventually_ge_atTop (1:ℝ)),
    hlim.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with x hm hx hB hs
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hB0 : 0 < B x := by linarith only [hB]
  have hsize : (3/5:ℝ)*(m x:ℝ) ≤ B x := by
    have hh := Real.log_le_log (Real.exp_pos _) hm
    rw [Real.log_exp] at hh
    have hl := Real.log_le_sub_one_of_pos hB0
    linarith only [hh,hl]
  have hsq : (m x:ℝ)^2/4 ≤ (B x)^2 := by
    have hnat := Nat.cast_nonneg (α:=ℝ) (m x)
    have hd : (m x:ℝ) ≤ 2*B x := by linarith only [hsize,hB]
    nlinarith only [mul_nonneg hnat (sub_nonneg.mpr hd),sq_nonneg (2*B x-(m x:ℝ))]
  change 4*((B x)^(2:ℝ)*Real.exp (-(1:ℝ)*B x)+
    (B x)^(1:ℝ)*Real.exp (-(1:ℝ)*B x)) < 1 at hs
  rw [Real.rpow_two,Real.rpow_one] at hs
  have he : Real.exp (B x)=Real.log x := Real.exp_log hlog
  have hbudget : 4*((B x)^2+B x) ≤ Real.log x := by
    have hh := mul_le_mul_of_nonneg_right hs.le (Real.exp_pos (B x)).le
    have hn : Real.exp (-(1:ℝ)*B x)*Real.exp (B x)=1 := by
      rw [← Real.exp_add]
      simp
    calc
      _ = (4*((B x)^2*Real.exp (-(1:ℝ)*B x)+B x*Real.exp (-(1:ℝ)*B x)))*Real.exp (B x) := by
        calc
          _ = 4*((B x)^2+B x)*(Real.exp (-(1:ℝ)*B x)*Real.exp (B x)) := by rw [hn]; ring
          _ = _ := by ring
      _ ≤ 1*Real.exp (B x) := hh
      _ = _ := by rw [one_mul,he]
  have hratio : x/Real.log x=Real.exp (Real.log x-B x) := by
    rw [Real.exp_sub,Real.exp_log (zero_lt_one.trans hx),he]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx),hratio,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hbudget,hsq]

lemma small_value_gaussian_count : ∀ᶠ x : ℝ in atTop,
    ∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,0 < v ∧ (v:ℝ) ≤ x^(3/4:ℝ)) →
    (Q.card:ℝ) ≤ (x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  filter_upwards [small_value_gaussian_scale,central_volume_one_le,
    eventually_gt_atTop (1:ℝ)] with x hx hG hx1
  intro Ψ hΨ Q hQ
  have hsub : Q ⊆ Finset.Icc 1 ⌊x^(3/4:ℝ)⌋₊ := by
    intro v hv
    exact Finset.mem_Icc.mpr ⟨(hQ v hv).1,Nat.le_floor (hQ v hv).2⟩
  have hc : (Q.card:ℝ) ≤ x^(3/4:ℝ) := by
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (Real.rpow_nonneg (by linarith only [hx1]) _))
  have hs : (Ψ:ℝ)^2 ≤ (m x:ℝ)^2 := by
    have hh : (Ψ:ℝ) ≤ m x := by exact_mod_cast hΨ
    nlinarith only [hh,Nat.cast_nonneg (α:=ℝ) Ψ,Nat.cast_nonneg (α:=ℝ) (m x)]
  have hf : 0 ≤ x/Real.log x := div_nonneg (by linarith only [hx1]) (Real.log_pos hx1).le
  calc
    _ ≤ (x/Real.log x)*Real.exp (-(m x:ℝ)^2/4) := hc.trans hx
    _ ≤ (x/Real.log x)*Real.exp (-(Ψ:ℝ)^2/4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hs])) hf
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hG hf
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le

end TotientAsymptotic

end

end OAI
