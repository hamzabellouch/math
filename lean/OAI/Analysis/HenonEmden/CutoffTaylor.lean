import OAI.Analysis.HenonEmden.AngularPressure

namespace OAI

universe uE

section CutoffTaylor

open Set Metric
noncomputable section
namespace HenonLaneEmden.Cutoff

lemma derivativeProfile_oscillation {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ}
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |derivativeProfile n s-derivativeProfile n r| ≤ secondConstant n*D^(N n-2)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_derivativeProfile hn t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖secondProfile n t‖ ≤ secondConstant n*D^(N n-2) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (secondProfile_bound hn t).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht) _) (constants_nonneg n).2.1))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

lemma etaProfile_oscillation (n : ℕ) {r s D : ℝ}
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |etaProfile n s-etaProfile n r| ≤ derivativeConstant n*D^(N n-1)*|s-r| := by
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_etaProfile n t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖derivativeProfile n t‖ ≤ derivativeConstant n*D^(N n-1) from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (derivativeProfile_bound n t).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (gapProfile_nonneg t) (hseg t ht) _) (constants_nonneg n).1))
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

lemma abs_sub_left_le_of_mem_uIcc {r s t : ℝ} (ht : t ∈ uIcc r s) : |t-r| ≤ |s-r| := by
  rcases le_total r s with h | h
  · rw [uIcc_of_le h] at ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1),abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [ht.2]
  · rw [uIcc_of_ge h] at ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2),abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [ht.1]

lemma etaProfile_taylor {n : ℕ} (hn : 1 ≤ n) {r s D : ℝ} (hD : 0 ≤ D)
    (hseg : ∀ t ∈ uIcc r s, gapProfile t ≤ D) :
    |etaProfile n s-etaProfile n r-derivativeProfile n r*(s-r)| ≤
      secondConstant n*D^(N n-2)*(s-r)^2 := by
  let F (t : ℝ) := etaProfile n t-derivativeProfile n r*t
  have hF (t) : HasDerivAt F (derivativeProfile n t-derivativeProfile n r) t := by
    convert (hasDerivAt_etaProfile n t).sub ((hasDerivAt_id t).const_mul (derivativeProfile n r)) using 1 <;> first | rfl | simp only [mul_one]
  have hh := (convex_uIcc r s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hF t).hasDerivWithinAt)
    (show ∀ t ∈ uIcc r s, ‖derivativeProfile n t-derivativeProfile n r‖ ≤ secondConstant n*D^(N n-2)*|s-r| from by
      intro t ht
      rw [Real.norm_eq_abs]
      exact (derivativeProfile_oscillation hn (fun z hz => hseg z (uIcc_subset_uIcc_left ht hz))).trans
        (mul_le_mul_of_nonneg_left (abs_sub_left_le_of_mem_uIcc ht)
          (mul_nonneg (constants_nonneg n).2.1 (pow_nonneg hD _))))
    left_mem_uIcc right_mem_uIcc
  simpa only [F,Real.norm_eq_abs,show etaProfile n s-derivativeProfile n r*s-(etaProfile n r-derivativeProfile n r*r) =
    etaProfile n s-etaProfile n r-derivativeProfile n r*(s-r) by ring,mul_assoc,← sq, sq_abs] using hh

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E] in
lemma eta_oscillation (n : ℕ) {x y : E} {D : ℝ} (hD : 0 ≤ D)
    (hxy : d x+dist x y ≤ D) :
    |eta n y-eta n x| ≤ derivativeConstant n*D^(N n-1)*dist x y := by
  have hh := etaProfile_oscillation n (fun t ht => (norm_segment_gap hxy ht).2)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (by simpa only [dist_comm x y,dist_eq_norm] using abs_norm_sub_norm_le y x)
    (mul_nonneg (constants_nonneg n).1 (pow_nonneg hD _)))

end HenonLaneEmden.Cutoff
end
end CutoffTaylor

end OAI
