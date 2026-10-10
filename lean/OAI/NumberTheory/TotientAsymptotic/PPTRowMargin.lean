import OAI.NumberTheory.TotientAsymptotic.GeometricCube
import OAI.NumberTheory.TotientAsymptotic.PPTNormalizedParameters

namespace OAI

/-!
The relaxed geometric family retains the row and adjacent-coordinate
margins required by the PPT comparison construction.  A bounded change
of the normalizing head coordinate consumes only part of that margin.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma ppt_half_row_error_bounds (r : ℕ) :
    0 < rowContractionError r/2 ∧ rowContractionError r/2 ≤ 1 := by
  have hr : (1 : ℝ) ≤ (r : ℝ)+1 := by
    linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hp : (1 : ℝ) ≤ ((r : ℝ)+1)^3 := one_le_pow₀ hr
  unfold rowContractionError
  constructor
  · positivity
  · rw [div_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 5*((r : ℝ)+1)^3*2)).mpr
    nlinarith

lemma ppt_row_budget_after_head_error {R H T e ω : ℝ} (hT : 0 < T)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hrow : R ≤ H/(1+ω))
    (hhead : H ≤ T+e) (herr : 4*e ≤ ω*T) :
    R ≤ (1-ω/4)*T := by
  have hden : 0 < 1+ω := by linarith
  apply hrow.trans
  apply (div_le_div_of_nonneg_right hhead hden.le).trans
  apply (div_le_iff₀ hden).mpr
  have hsq : ω^2 ≤ ω := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq hT.le
  nlinarith

/-- The explicit inverse-cube row budget is retained under a head error
of at most a quarter of the relaxed row margin. -/
theorem ppt_relaxed_row_budget {m n : ℕ} {B c T e : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ relaxedGeometricFamily m n B c) (i : Fin n)
    (hT : 0 < T) (hhead : v i ≤ T+e)
    (herr : 4*e ≤ (rowContractionError (m-(i.val+1))/2)*T) :
    (∑ j : Fin n, if i < j then a (j.val-i.val)*v j else 0) ≤
      (1-rowContractionError (m-(i.val+1))/8)*T := by
  have hω := ppt_half_row_error_bounds (m-(i.val+1))
  have hh := ppt_row_budget_after_head_error hT hω.1 hω.2
    (hv.1.2.2.1 i) hhead herr
  convert hh using 1
  ring

theorem ppt_relaxed_top_budget {m n : ℕ} {B c : ℝ} {v : Fin n → ℝ}
    (hv : v ∈ relaxedGeometricFamily m n B c) (hB : 0 < B) :
    (∑ i : Fin n, a (i.val+1)*v i) ≤ (1-rowContractionError m/8)*B := by
  have hω := ppt_half_row_error_bounds m
  have hh := ppt_row_budget_after_head_error (R := ∑ i : Fin n, a (i.val+1)*v i)
    (H := B) (e := 0) hB hω.1 hω.2 hv.1.2.2.2 (by linarith)
    (by simpa only [mul_zero] using mul_nonneg hω.1.le hB.le)
  convert hh using 1
  ring

lemma ppt_normalized_contracted_coordinate {U H T e η ω ν : ℝ}
    (hT : 0 < T) (hω : 0 < ω) (he : 0 ≤ e)
    (hgap : U ≤ H/(1+ω)) (hhead : H ≤ T+e) (hν : ν ≤ U/T+η) :
    ν ≤ 1/(1+ω)+(e/T+η) := by
  have hden : 0 < 1+ω := by linarith
  have hnum : U ≤ T/(1+ω)+e := by
    apply hgap.trans
    apply (div_le_div_of_nonneg_right hhead hden.le).trans
    apply (div_le_iff₀ hden).mpr
    rw [add_mul, div_mul_cancel₀ _ hden.ne']
    have hprod : 0 ≤ e*ω := mul_nonneg he hω.le
    nlinarith
  apply hν.trans
  calc
    U/T+η ≤ (T/(1+ω)+e)/T+η := by
      linarith only [div_le_div_of_nonneg_right hnum hT.le]
    _ = 1/(1+ω)+(e/T+η) := by
      rw [add_div, div_right_comm T (1+ω) T, div_self hT.ne']
      ring

/-- The pairwise margin of the actual relaxed family supplies the
first-cutoff condition once head and grid errors fit in its budget. -/
theorem ppt_relaxed_first_cutoff_loss {m n : ℕ} {B c T e η ν : ℝ}
    {v : Fin n → ℝ} (hv : v ∈ relaxedGeometricFamily m n B c)
    (i j : Fin n) (hij : i < j) (hT : 0 < T) (he : 0 ≤ e)
    (hhead : v i ≤ T+e) (hν : ν ≤ v j/T+η)
    (herr : 4*(e/T+η) ≤ rowContractionError (m-(i.val+1))/2)
    (hbudget : 4*Real.log (10*T) ≤ T*(rowContractionError (m-(i.val+1))/2)) :
    Real.log (10*T) ≤ T*(1-ν) := by
  have hω := ppt_half_row_error_bounds (m-(i.val+1))
  have hn := ppt_normalized_contracted_coordinate hT hω.1 he
    (hv.2.2 i j hij) hhead hν
  exact ppt_log_loss_of_contracted_coordinate hT hω.1 hω.2 hn herr hbudget

end TotientAsymptotic

end

end OAI
