import OAI.Analysis.Pureness.Stabilization.FixedCut

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace

def squareCutMultiplier (δ : ℝ≥0) (t : ℝ) : ℝ :=
  Real.sqrt (max (t - δ) 0) / max t δ

lemma squareCutMultiplier_continuous {δ : ℝ≥0} (hδ : 0 < δ) :
    Continuous (squareCutMultiplier δ) := by
  exact (Real.continuous_sqrt.comp ((continuous_id.sub continuous_const).max continuous_const)).div
    (continuous_id.max continuous_const) (fun t => ne_of_gt
      (lt_of_lt_of_le hδ (le_max_right _ _)))

lemma squareCutMultiplier_zero (δ : ℝ≥0) : squareCutMultiplier δ 0 = 0 := by
  simp [squareCutMultiplier]

lemma squareCutMultiplier_identity {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    squareCutMultiplier δ t * (t * t) * squareCutMultiplier δ t = max (t - δ) 0 := by
  by_cases ht : t ≤ δ
  · simp [squareCutMultiplier, max_eq_right (sub_nonpos.mpr ht)]
  · have ht0 : 0 < t := lt_trans hδ (lt_of_not_ge ht)
    unfold squareCutMultiplier
    rw [max_eq_left (le_of_not_ge ht)]
    calc
      Real.sqrt (max (t - δ) 0) / t * (t * t) * (Real.sqrt (max (t - δ) 0) / t) =
          Real.sqrt (max (t - δ) 0) ^ 2 := by field_simp
      _ = _ := Real.sq_sqrt (le_max_right _ _)

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem starMul_cut_factorization (x : A) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ v : A, star v * (x * star x) * v = (Positive.cut δ (Positive.starMul x)).1 := by
  let a := Positive.starMul x
  let f := squareCutMultiplier δ
  have hf : Continuous f := squareCutMultiplier_continuous hδ
  have hf0 : f 0 = 0 := squareCutMultiplier_zero δ
  have ha : IsSelfAdjoint a.1 := IsSelfAdjoint.of_nonneg a.2
  let g : A := cfcₙ f a.1
  have hg : star g = g := (cfcₙ_predicate f a.1).star_eq
  refine ⟨x * g, ?_⟩
  rw [star_mul, hg]
  calc
    g * star x * (x * star x) * (x * g) = g * (a.1 * a.1) * g := by
      dsimp [a, Positive.starMul]
      noncomm_ring
    _ = cfcₙ (fun t : ℝ => f t * (t * t) * f t) a.1 := by
      dsimp [g]
      rw [cfcₙ_mul (fun t : ℝ => f t * (t * t)) f a.1,
        cfcₙ_mul f (fun t : ℝ => t * t) a.1,
        cfcₙ_mul (fun t : ℝ => t) (fun t : ℝ => t) a.1, cfcₙ_id' ℝ a.1]
    _ = (Positive.cut δ a).1 := cfcₙ_congr fun t _ => squareCutMultiplier_identity hδ t

theorem starMul_cuntzBelow_mulStar (x : A) :
    CuntzBelow (Positive.starMul x) (Positive.mulStar x) := by
  apply CuntzBelow.of_cuts
  intro δ hδ η hη
  obtain ⟨v, hv⟩ := starMul_cut_factorization x δ hδ
  exact ⟨v, by simpa [Positive.mulStar, hv] using hη⟩

theorem mulStar_cuntzBelow_starMul (x : A) :
    CuntzBelow (Positive.mulStar x) (Positive.starMul x) := by
  simpa only [Positive.mulStar, Positive.starMul, star_star] using
    starMul_cuntzBelow_mulStar (star x)

theorem starMul_cuntzBelow_iff (x : A) (b : Positive A) :
    CuntzBelow (Positive.starMul x) b ↔ CuntzBelow (Positive.mulStar x) b := by
  exact ⟨fun h => (mulStar_cuntzBelow_starMul x).trans h,
    fun h => (starMul_cuntzBelow_mulStar x).trans h⟩

end CuntzTrace

end

end OAI
