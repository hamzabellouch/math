import OAI.Analysis.Pureness.Stabilization.AbsoluteComparison

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def truncationMultiplier (δ : ℝ≥0) (t : ℝ) : ℝ := max (t-δ) 0 / max t δ
lemma truncationMultiplier_continuous {δ : ℝ≥0} (hδ : 0 < δ) :
    Continuous (truncationMultiplier δ) :=
  ((continuous_id.sub continuous_const).max continuous_const).div
    (continuous_id.max continuous_const) (fun _ => ne_of_gt (lt_of_lt_of_le hδ (le_max_right _ _)))
lemma truncationMultiplier_zero (δ : ℝ≥0) : truncationMultiplier δ 0 = 0 := by simp [truncationMultiplier]
lemma truncationMultiplier_identity {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    t * truncationMultiplier δ t = max (t-δ) 0 := by
  by_cases ht : t ≤ δ
  · simp [truncationMultiplier, max_eq_right (sub_nonpos.mpr ht)]
  · have ht0 : 0 < t := lt_trans hδ (lt_of_not_ge ht)
    simp only [truncationMultiplier, max_eq_left (le_of_not_ge ht)]
    field_simp

theorem exists_cut_truncation (x : A) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ z : A, ‖x-z‖ ≤ δ ∧ Positive.abs z = Positive.cut δ (Positive.abs x) := by
  let a := Positive.abs x
  let c := Positive.cut δ a
  let f := truncationMultiplier δ
  have hf : Continuous f := truncationMultiplier_continuous hδ
  have hf0 : f 0 = 0 := truncationMultiplier_zero δ
  have ha := IsSelfAdjoint.of_nonneg a.2
  let q := cfcₙ f a.1
  have hqs : star q = q := (cfcₙ_predicate f a.1).star_eq
  have haq : a.1*q = c.1 := by
    dsimp [q]
    calc
      _ = cfcₙ (fun t : ℝ => t*f t) a.1 := by rw [cfcₙ_mul (fun t : ℝ => t) f a.1, cfcₙ_id' ℝ a.1]
      _ = c.1 := cfcₙ_congr (fun t _ => truncationMultiplier_identity hδ t)
  have hax : a.1*a.1 = star x*x := Positive.abs_sq x
  have hid (z : A) : star (x*z)*(x*z) = star (a.1*z)*(a.1*z) := by
    rw [star_mul, star_mul, ha.star_eq]
    calc
      _ = star z*(star x*x)*z := by noncomm_ring
      _ = star z*(a.1*a.1)*z := by rw [hax]
      _ = _ := by noncomm_ring
  have hdiff : star (x-x*q)*(x-x*q) = star (a.1-a.1*q)*(a.1-a.1*q) := by
    simp only [star_sub, star_mul, ha.star_eq, hqs]
    calc
      _ = star x*x - (star x*x)*q - q*(star x*x) + q*(star x*x)*q := by noncomm_ring
      _ = (a.1*a.1) - (a.1*a.1)*q - q*(a.1*a.1) + q*(a.1*a.1)*q := by rw [hax]
      _ = _ := by noncomm_ring
  have hn : ‖x-x*q‖ = ‖a.1-c.1‖ := by
    have h := congrArg norm hdiff
    rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self, haq] at h
    nlinarith [norm_nonneg (x-x*q), norm_nonneg (a.1-c.1)]
  refine ⟨x*q, hn ▸ Positive.norm_sub_cut_le δ a, ?_⟩
  apply Subtype.ext
  change CFC.sqrt (star (x*q)*(x*q)) = c.1
  rw [hid, haq, c.2.star_eq]
  exact CFC.sqrt_mul_self c.1 c.2
end CuntzTrace

end

end OAI
