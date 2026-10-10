import OAI.Geometry.Relativity.CKS.RadialProfiles

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

def roundingWeight (R r : ℝ) : ℝ := Real.smoothTransition (r/R-2)
lemma roundingWeight_smooth (R : ℝ) : ContDiff ℝ ∞ (roundingWeight R) := by
  unfold roundingWeight
  fun_prop
lemma roundingWeight_nonneg (R r : ℝ) : 0 ≤ roundingWeight R r := Real.smoothTransition.nonneg _
lemma roundingWeight_le_one (R r : ℝ) : roundingWeight R r ≤ 1 := Real.smoothTransition.le_one _
lemma roundingWeight_zero {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) : roundingWeight R r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h := (div_le_iff₀ hR).mpr hr
  linarith
lemma roundingWeight_one {R r : ℝ} (hR : 0 < R) (hr : 3*R ≤ r) : roundingWeight R r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := (le_div_iff₀ hR).mpr hr
  linarith
lemma roundingWeight_le_paddingWeight (R r : ℝ) : roundingWeight R r ≤ paddingWeight R r := by
  apply Real.smoothTransition.monotone
  linarith
lemma roundingWeight_deriv_initial {R r : ℝ} (hR : 0 < R) (hr : r ≤ 2*R) :
    deriv (roundingWeight R) r = 0 := by
  have hm : IsLocalMin (roundingWeight R) r := by
    apply Filter.Eventually.of_forall
    intro y
    rw [roundingWeight_zero hR hr]
    exact roundingWeight_nonneg R y
  exact hm.deriv_eq_zero
lemma roundingWeight_deriv (R r : ℝ) :
    deriv (roundingWeight R) r = deriv Real.smoothTransition (r/R-2)/R := by
  have hi : HasDerivAt (fun t : ℝ => t/R-2) (1/R) r := by
    simpa using ((hasDerivAt_id r).div_const R).sub_const 2
  have ho := (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable (by simp) (r/R-2)
  have hh : HasDerivAt (roundingWeight R) (deriv Real.smoothTransition (r/R-2)/R) r := by
    convert! ho.hasDerivAt.comp r hi using 1
    ring
  exact hh.deriv

theorem roundingWeight_weighted_deriv :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R r : ℝ, 0 < R → R ≤ r → r ≤ 3*R →
      |r*deriv (roundingWeight R) r| ≤ B*paddingWeight R r := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0:ℝ) 1)
  refine ⟨3*max C 0,by positivity,?_⟩
  intro R r hR hRr hr
  by_cases hlow : r ≤ 2*R
  · rw [roundingWeight_deriv_initial hR hlow,mul_zero,abs_zero]
    exact mul_nonneg (by positivity) (paddingWeight_nonneg R r)
  have hw : paddingWeight R r = 1 := paddingWeight_one hR (lt_of_not_ge hlow).le
  rw [hw,mul_one,roundingWeight_deriv]
  have h0 : 0 ≤ r/R-2 := by
    have hh : 2 ≤ r/R := (le_div_iff₀ hR).mpr (lt_of_not_ge hlow).le
    linarith
  have h1 : r/R-2 ≤ 1 := by
    have hh : r/R ≤ 3 := (div_le_iff₀ hR).mpr hr
    linarith
  have hd0 : |deriv Real.smoothTransition (r/R-2)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (r/R-2) ⟨h0,h1⟩
  have hd : |deriv Real.smoothTransition (r/R-2)| ≤ max C 0 := hd0.trans (le_max_left _ _)
  have hrr : 0 ≤ r/R := div_nonneg (hR.le.trans hRr) hR.le
  have hrr3 : r/R ≤ 3 := (div_le_iff₀ hR).mpr hr
  calc
    |r*(deriv Real.smoothTransition (r/R-2)/R)| = |r/R| *|deriv Real.smoothTransition (r/R-2)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ 3*max C 0 := by
      rw [abs_of_nonneg hrr]
      exact mul_le_mul hrr3 hd (abs_nonneg _) (by norm_num)

end
end CKSBending

end

end OAI
