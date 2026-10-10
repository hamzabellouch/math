import OAI.Analysis.BernoulliCone.HalfspaceQuotient

namespace OAI

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal ContDiff
namespace Bernoulli.Halfspace
variable {d : ℕ}
/-- The square perspective on the nonnegative cone, with its zero value at
zero denominator. Used on actual admissible Lipschitz variations. -/
def positiveSquareRatio (v u : Space d → ℝ) (x : Space d) : ℝ :=
  if 0<u x then v x^2/u x else 0

lemma positiveSquareRatio_nonneg {v u : Space d → ℝ} (x : Space d) :
    0 ≤ positiveSquareRatio v u x := by
  by_cases h : 0<u x
  · simp only [positiveSquareRatio,ite_eq_left h]; positivity
  · simp [positiveSquareRatio,h]

lemma positiveSquareRatio_bound {v u : Space d → ℝ} {C : ℝ} (_hC : 0≤C)
    (hu : ∀x, 0≤u x) (hv : ∀x, |v x| ≤ C*u x) (x : Space d) :
    positiveSquareRatio v u x ≤ C^2*u x := by
  by_cases h : 0<u x
  · simp only [positiveSquareRatio,ite_eq_left h]
    apply (div_le_iff₀ h).mpr
    have hh := pow_le_pow_left₀ (abs_nonneg (v x)) (hv x) 2
    simp only [sq_abs,mul_pow] at hh
    nlinarith
  · simp only [positiveSquareRatio,ite_eq_right h]
    exact mul_nonneg (sq_nonneg C) (hu x)

lemma positiveSquareRatio_lipschitz {v u : Space d → ℝ} {L M : ℝ≥0}
    (hL : LipschitzWith L u) (hM : LipschitzWith M v)
    {C : ℝ≥0} (hC : 1≤C) (hu : ∀x, 0≤u x) (hv : ∀x, |v x| ≤ (C:ℝ)*u x) :
    LipschitzWith (3*C^2*max L M) (positiveSquareRatio v u) := by
  have hc : 1≤(C:ℝ) := hC
  have hb (x y : Space d) : |v x-v y| ≤ (C:ℝ)*((max L M:ℝ≥0):ℝ)*dist x y := by
    have hh := hM.norm_sub_le x y
    rw [Real.norm_eq_abs,←dist_eq_norm] at hh
    refine hh.trans ?_
    gcongr
    exact (show (M:ℝ)≤((max L M:ℝ≥0):ℝ) from le_max_right _ _).trans
      (le_mul_of_one_le_left (by positivity) hc)
  have hd (x y : Space d) : u x-u y ≤ ((max L M:ℝ≥0):ℝ)*dist x y := by
    have hh := hL.norm_sub_le x y
    rw [Real.norm_eq_abs,←dist_eq_norm] at hh
    exact (le_abs_self _).trans (hh.trans (by gcongr; exact le_max_left _ _))
  have hmain (x y : Space d) (hxy : u y≤u x) :
      |positiveSquareRatio v u x-positiveSquareRatio v u y| ≤
        (3*(C:ℝ)^2*((max L M:ℝ≥0):ℝ))*dist x y := by
    by_cases hx : 0<u x
    · by_cases hy : 0<u y
      · simp only [positiveSquareRatio,ite_eq_left hx,ite_eq_left hy]
        have hh := perspective_estimate C.coe_nonneg (mul_nonneg (by positivity) dist_nonneg)
          hx hy hxy (hv x) (hv y) (by simpa only [mul_assoc] using hb x y) (hd x y)
        simpa only [mul_assoc] using hh
      · have hy0 : u y=0 := le_antisymm (not_lt.mp hy) (hu y)
        simp only [positiveSquareRatio,ite_eq_left hx,ite_eq_right hy,sub_zero,
          abs_of_nonneg (div_nonneg (sq_nonneg _) hx.le)]
        calc
          _ ≤ (C:ℝ)^2*u x := by
            simpa only [positiveSquareRatio,ite_eq_left hx] using positiveSquareRatio_bound C.coe_nonneg hu hv x
          _ ≤ (C:ℝ)^2*(((max L M:ℝ≥0):ℝ)*dist x y) := by
            gcongr
            simpa only [hy0,sub_zero] using hd x y
          _ ≤ _ := by
            have hp : 0 ≤ (C:ℝ)^2*(((max L M:ℝ≥0):ℝ)*dist x y) := by positivity
            nlinarith
    · have hy : ¬0<u y := by linarith
      simp only [positiveSquareRatio,ite_eq_right hx,ite_eq_right hy,sub_self,abs_zero]
      positivity
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change _ ≤ (3*(C:ℝ)^2*((max L M:ℝ≥0):ℝ))*dist x y
  obtain hh|hh := le_total (u y) (u x)
  · exact hmain x y hh
  · simpa only [abs_sub_comm,dist_comm] using hmain y x hh
end Bernoulli.Halfspace

end
end

end OAI
