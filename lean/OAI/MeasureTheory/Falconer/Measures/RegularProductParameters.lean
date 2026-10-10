import OAI.MeasureTheory.Falconer.Estimates.ScalarScaleAlignment

namespace OAI

/-! Uniform weak losses for the regular product incidence estimate. -/
namespace Falconer

 theorem regular_product_parameters {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      let x := (N:ℝ)*Real.log 2
      let D := Real.exp (ε*x)
      let R := Real.exp (η*x)
      let W := Real.exp (θ*x)
      1 ≤ D ∧ 1 ≤ R ∧ 4*R ≤ W ∧ 4*R*D ≤ W ∧
        4*R^2*(16+400*D^4) ≤ W ∧ 2450*D^4 ≤ W ∧
        Real.log 7+ε*x ≤ 4*κ*x ∧ 25*D^2 ≤ Real.exp ((η/2)*x) := by
  let η := min θ κ/100
  let ε := η/100
  have hη : 0 < η := by dsimp [η]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hηθ : η ≤ θ/100 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηκ : η ≤ κ/100 := by
    dsimp [η]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hεη : ε = η/100 := rfl
  obtain ⟨N1,hN1,hcost⟩ := scalar_fixed_losses hθ (by norm_num : (0:ℝ) < 1664) (by norm_num : (0:ℝ) < 2450)
  obtain ⟨N2,hN2,hsmall⟩ := scalar_fixed_losses (by positivity : 0 < η/2)
    (by norm_num : (0:ℝ) < 25) (by norm_num : (0:ℝ) < 7)
  refine ⟨ε,η,max N1 N2,hε,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro N hN
  dsimp only
  let x := (N:ℝ)*Real.log 2
  let D := Real.exp (ε*x)
  let R := Real.exp (η*x)
  let W := Real.exp (θ*x)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (mul_nonneg hε.le hx)
  have hR : 1 ≤ R := Real.one_le_exp_iff.mpr (mul_nonneg hη.le hx)
  obtain ⟨h1664,h2450⟩ := hcost N ((le_max_left _ _).trans hN)
  obtain ⟨h25,h7⟩ := hsmall N ((le_max_right _ _).trans hN)
  have hpoly : R^2*D^4 ≤ Real.exp ((θ/4)*x) := by
    change (Real.exp (η*x))^2*(Real.exp (ε*x))^4 ≤ _
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : 2*η+4*ε ≤ θ/4 := by rw [hεη]; linarith only [hηθ,hη]
    have hm := mul_le_mul_of_nonneg_right hh hx
    nlinarith only [hm]
  have hbase : 1664*R^2*D^4 ≤ W := by
    calc
      _ = 1664*(R^2*D^4) := by ring
      _ ≤ 1664*Real.exp ((θ/4)*x) := mul_le_mul_of_nonneg_left hpoly (by norm_num)
      _ ≤ W := by simpa only [x,W,mul_assoc] using h1664
  have hR2 : R ≤ R^2 := by nlinarith only [hR]
  have hD4 : 1 ≤ D^4 := one_le_pow₀ hD
  have hD14 : D ≤ D^4 := by simpa only [pow_one] using pow_le_pow_right₀ hD (show 1 ≤ (4:ℕ) by omega)
  have hR2pos : 0 ≤ R^2 := sq_nonneg R
  have hRbase : 4*R ≤ 1664*R^2*D^4 := by
    have hm := mul_le_mul_of_nonneg_left hD4 hR2pos
    nlinarith only [hR2,hR,hR2pos,hm]
  have hRDbase : 4*R*D ≤ 1664*R^2*D^4 := by
    have hm := mul_le_mul hR2 hD14 (zero_le_one.trans hD) hR2pos
    have hp : 0 ≤ R*D := by positivity
    nlinarith only [hm,hp]
  have hG : 4*R^2*(16+400*D^4) ≤ W := by
    have hh : 16+400*D^4 ≤ 416*D^4 := by linarith only [hD4]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*R^2 by positivity)
    exact hm.trans_eq (by ring) |>.trans hbase
  have hDpoly : D^4 ≤ Real.exp ((θ/4)*x) := by
    have hm := mul_le_mul_of_nonneg_right (show 1 ≤ R^2 by nlinarith only [hR]) (pow_nonneg (zero_le_one.trans hD) 4)
    have hmul : D^4 ≤ R^2*D^4 := by simpa only [one_mul] using hm
    exact hmul.trans hpoly
  have hP : 2450*D^4 ≤ W :=
    (mul_le_mul_of_nonneg_left hDpoly (by norm_num)).trans (by
      simpa only [x,W,mul_assoc] using h2450)
  have hsmallD : D^2 ≤ Real.exp ((η/8)*x) := by
    change (Real.exp (ε*x))^2 ≤ _
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hh : 2*ε ≤ η/8 := by rw [hεη]; linarith only [hη]
    have hm := mul_le_mul_of_nonneg_right hh hx
    nlinarith only [hm]
  have h25' : 25*D^2 ≤ Real.exp ((η/2)*x) := by
    apply (mul_le_mul_of_nonneg_left hsmallD (by norm_num)).trans
    have he : (η/2/4)*(N:ℝ)*Real.log 2 = (η/8)*x := by dsimp [x]; ring
    have he' : (η/2)*(N:ℝ)*Real.log 2 = (η/2)*x := by dsimp [x]; ring
    rwa [he,he'] at h25
  have h7log : Real.log 7+(η/8)*x ≤ (η/2)*x := by
    have hh := Real.log_le_log (by positivity : (0:ℝ) < 7*Real.exp (((η/2)/4)*(N:ℝ)*Real.log 2)) h7
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp,Real.log_exp] at hh
    convert hh using 1 <;> dsimp [x] <;> ring
  have hlog : Real.log 7+ε*x ≤ 4*κ*x := by
    have he : ε ≤ κ := by rw [hεη]; linarith only [hηκ,hκ]
    have hh := mul_le_mul_of_nonneg_right hηκ hx
    have he' := mul_le_mul_of_nonneg_right he hx
    nlinarith only [h7log,hh,he',hx,hη,hκ]
  exact ⟨hD,hR,hRbase.trans hbase,hRDbase.trans hbase,hG,hP,hlog,h25'⟩

end Falconer

end OAI
