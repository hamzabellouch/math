import OAI.NumberTheory.JointDickman.Amplification.MultiplicityRates
import OAI.NumberTheory.JointDickman.Amplification.ParameterEstimates

namespace OAI

/-! # The clamped Rankin exponent for numeric additions -/

namespace JointDickman

/-- The entropy exponent from the numeric sieve loses at most the clamp.
This includes both the zero-cardinality class and counts exceeding half the
prefix mean. -/
theorem clamped_numeric_rankin {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let r := min x (1/2)
    let q := max δ r
    q+x*Real.log ((1/2)/q) ≤ halfRankinExponent r+δ := by
  dsimp only
  by_cases hx1 : x ≤ 1/2
  · rw [min_eq_left hx1]
    by_cases hd : δ ≤ x
    · rw [max_eq_right hd]
      unfold halfRankinExponent
      nlinarith
    · rw [max_eq_left (le_of_not_ge hd)]
      by_cases hx0 : x = 0
      · subst x
        simp [halfRankinExponent]
      · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
        have hfrac : (1/2 : ℝ)/δ ≤ (1/2 : ℝ)/x :=
          div_le_div_of_nonneg_left (by norm_num) hxpos (le_of_not_ge hd)
        have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (1/2 : ℝ)/δ) hfrac
        have hm := mul_le_mul_of_nonneg_left hlog hx
        unfold halfRankinExponent
        nlinarith
  · rw [min_eq_right (le_of_not_ge hx1),max_eq_right hδ1]
    norm_num [halfRankinExponent]
    exact hδ.le

theorem halfRankinExponent_le_half {r : ℝ} (hr : 0 ≤ r) : halfRankinExponent r ≤ 1/2 := by
  by_cases hr0 : r = 0
  · simp [hr0,halfRankinExponent]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (1/2 : ℝ)/r)
    have hh := mul_le_mul_of_nonneg_left hlog hr
    have he : r*((1/2 : ℝ)/r-1) = 1/2-r := by field_simp
    rw [he] at hh
    unfold halfRankinExponent
    nlinarith

/-- The grid cutoff contributes at most 3Δ when g-γ=2Δ; the clamp
contributes at most gδ. -/
theorem numeric_rankin_exponent_bound {g γ τ x δ : ℝ}
    (hg : 0 ≤ g) (hγ : γ ≤ g) (hx : 0 ≤ x) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let r := min x (1/2);
    let q := max δ r;
    -(3/2-q)*γ+g*x*Real.log ((1/2)/q)+(g/2+τ)*Real.log 2 ≤
      g*(halfRankinExponent r-1-weightBaseExponent)+
        (3/2)*(g-γ)+g*δ+τ*Real.log 2 := by
  dsimp only
  have hclamp := clamped_numeric_rankin hx hδ hδ1
  have hmul := mul_le_mul_of_nonneg_left hclamp hg
  have hq : 0 ≤ max δ (min x (1/2)) := hδ.le.trans (le_max_left _ _)
  have hgap : 0 ≤ (g-γ)*max δ (min x (1/2)) := mul_nonneg (sub_nonneg.mpr hγ) hq
  unfold weightBaseExponent
  nlinarith

/-- The prefactor cannot grow with an unbounded cardinality: above the
clipping threshold its Rankin contribution is exactly one. -/
theorem numeric_rankin_prefactor_bound {g τ ℓ : ℝ} {d : ℕ} {δ : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hℓ : 0 < ℓ) (hτ : τ ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    let q := max δ (min ((d : ℝ)/(g*ℓ)) (1/2))
    ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2) ≤ Real.exp (3*ℓ) := by
  dsimp only
  let x := (d : ℝ)/(g*ℓ)
  let q := max δ (min x (1/2))
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (mul_pos hg hℓ).le
  have hq : 0 < q := hδ.trans_le (le_max_left _ _)
  have hr : 0 ≤ min x (1/2) := le_min hx (by norm_num)
  have hc := clamped_numeric_rankin hx hδ hδ1
  have hf := halfRankinExponent_le_half hr
  have hclamp : x*Real.log ((1/2 : ℝ)/q) ≤ 1 := by
    change q+x*Real.log ((1/2 : ℝ)/q) ≤ _ at hc
    linarith
  have hmul := mul_le_mul_of_nonneg_left hclamp (mul_pos hg hℓ).le
  have hxid : g*ℓ*x = (d : ℝ) := by dsimp only [x]; field_simp
  rw [← mul_assoc,hxid] at hmul
  have hd : (d : ℝ)*Real.log ((1/2 : ℝ)/q) ≤ ℓ := by
    have hgℓ := mul_le_mul_of_nonneg_right hg1 hℓ.le
    nlinarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    exact hh
  have hterm : (g/2+τ)*Real.log 2 ≤ 2 := by nlinarith
  have heq : ((1/2 : ℝ)/q)^d = Real.exp ((d : ℝ)*Real.log ((1/2 : ℝ)/q)) := by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
  change ((1/2 : ℝ)/q)^d*Real.exp (((g/2+τ)*ℓ)*Real.log 2) ≤ _
  rw [heq,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem halfRankinExponent_nonneg {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1/2) :
    0 ≤ halfRankinExponent r := by
  by_cases hr0 : r = 0
  · simp [hr0,halfRankinExponent]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hfrac : (1 : ℝ) ≤ (1/2 : ℝ)/r := (le_div_iff₀ hrpos).mpr (by linarith)
    have hlog := Real.log_nonneg hfrac
    unfold halfRankinExponent
    positivity

end JointDickman

end OAI
