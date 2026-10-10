import OAI.Probability.InvariantIsing.Fields.FieldSecondMeasurable

namespace OAI

/-! Uniform second-derivative bounds on a positive-variance interval.
The constants depend on the interval bounds but not on the spatial bias. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

private lemma affine_linear_integral_bound {I : Set ℝ} (F : FieldSmoothFamily I)
    (a v ζ : ℝ) (p : ℝ × ℝ) {V : ℝ} (hV : a + v * p.1 ≤ V)
    {A : ℝ → ℝ} (hA : Measurable A) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ u, |A u| ≤ C * (1 + |u|)) :
    |∫ u, A u ∂F.affineLaw a v ζ p| ≤ C * F.affineMomentCap ζ V := by
  apply F.affineLaw_integral_bound a v ζ p hV hA hC
  intro u
  exact (hB u).trans (mul_le_mul_of_nonneg_left (field_mark_one_add_le_sq u) hC)

namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

def mixedMeanCap (R ζ V : ℝ) : ℝ :=
  (F.KTX + F.KXX * R + 2 * |ζ| * F.KX * (F.KT + F.KX * R)) *
    F.toFieldSmoothFamily.affineMomentCap ζ V

def secondMeanCap (R D ζ V : ℝ) : ℝ :=
  (F.KTT + 2 * F.KTX * R + F.KXX * R ^ 2 + F.KX * D) *
      F.toFieldSmoothFamily.affineMomentCap ζ V +
    |ζ| * ((F.KT + F.KX * R) ^ 2 * F.toFieldSmoothFamily.affineMomentCap ζ V +
      ((F.KT + F.KX * R) * F.toFieldSmoothFamily.affineMomentCap ζ V) ^ 2)

lemma mixedMean_bound (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    {R V : ℝ} (hR : 0 ≤ R) (hc : |fieldAmplitudeSlope a v p.1| ≤ R)
    (hV : a + v * p.1 ≤ V) : |F.mixedMean a v ζ p| ≤ F.mixedMeanCap R ζ V := by
  let A := F.KT + F.KX * R
  let B := F.KTX + F.KXX * R
  let M := F.toFieldSmoothFamily.affineMomentCap ζ V
  let ν := F.toFieldSmoothFamily.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hXX : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hTX : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hiA : |∫ u, F.shiftedTangent a v u p ∂ν| ≤ A * M :=
    affine_linear_integral_bound F.toFieldSmoothFamily a v ζ p hV
      (F.measurable_shiftedTangent a v p) hA (fun u => F.shiftedTangent_bound a v u hp hR hc)
  have hiB : |∫ u, F.shiftedMixed a v u p ∂ν| ≤ B * M :=
    affine_linear_integral_bound F.toFieldSmoothFamily a v ζ p hV
      (F.measurable_shiftedMixed a v p) hB (fun u => F.shiftedMixed_bound a v u hp hR hc)
  have hiXA : |∫ u, F.shiftedMean a v u p * F.shiftedTangent a v u p ∂ν| ≤ F.KX * A * M := by
    apply affine_linear_integral_bound F.toFieldSmoothFamily a v ζ p hV
      ((F.measurable_shiftedMean a v p).mul (F.measurable_shiftedTangent a v p)) (mul_nonneg hX hA)
    intro u
    change |F.shiftedMean a v u p * F.shiftedTangent a v u p| ≤ _
    rw [abs_mul]
    calc
      _ ≤ F.KX * (A * (1 + |u|)) := mul_le_mul (F.bX _)
        (F.shiftedTangent_bound a v u hp hR hc) (abs_nonneg _) hX
      _ = _ := by ring
  have hiMean := F.bound_mean a v ζ p
  unfold mixedMean
  calc
    _ ≤ |∫ u, F.shiftedMixed a v u p ∂ν| +
        |ζ * ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v u p ∂ν) -
          F.mean a v ζ p * ∫ u, F.shiftedTangent a v u p ∂ν)| := abs_add_le _ _
    _ ≤ B * M + |ζ| * ((F.KX * A * M) + F.KX * (A * M)) := by
      apply add_le_add hiB
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
      refine (abs_sub _ _).trans (add_le_add hiXA ?_)
      rw [abs_mul]
      exact mul_le_mul hiMean hiA (abs_nonneg _) hX
    _ = F.mixedMeanCap R ζ V := by
      dsimp only [mixedMeanCap, A, B, M]
      ring

lemma secondMean_bound (a v ζ : ℝ) {p : ℝ × ℝ} (hp : p.1 ∈ I)
    {R D V : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hc : |fieldAmplitudeSlope a v p.1| ≤ R)
    (hd : |fieldAmplitudeCurvature a v p.1| ≤ D) (hV : a + v * p.1 ≤ V) :
    |F.secondMean a v ζ p| ≤ F.secondMeanCap R D ζ V := by
  let A := F.KT + F.KX * R
  let C := F.KTT + 2 * F.KTX * R + F.KXX * R ^ 2 + F.KX * D
  let M := F.toFieldSmoothFamily.affineMomentCap ζ V
  let ν := F.toFieldSmoothFamily.affineLaw a v ζ p
  have hX := F.kx_nonneg
  have hXX : 0 ≤ F.KXX := (abs_nonneg _).trans (F.bXX (0, 0))
  have hT : 0 ≤ F.KT := (abs_nonneg _).trans (F.bT (p.1, 0) hp)
  have hTX : 0 ≤ F.KTX := (abs_nonneg _).trans (F.bTX (p.1, 0) hp)
  have hTT : 0 ≤ F.KTT := (abs_nonneg _).trans (F.bTT (p.1, 0) hp)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hiA : |∫ u, F.shiftedTangent a v u p ∂ν| ≤ A * M :=
    affine_linear_integral_bound F.toFieldSmoothFamily a v ζ p hV
      (F.measurable_shiftedTangent a v p) hA (fun u => F.shiftedTangent_bound a v u hp hR hc)
  have hiC : |∫ u, F.shiftedSecond a v u p ∂ν| ≤ C * M :=
    F.toFieldSmoothFamily.affineLaw_integral_bound a v ζ p hV
      (F.measurable_shiftedSecond a v p) hC (fun u => F.shiftedSecond_bound a v u hp hR hD hc hd)
  have hiAA : |∫ u, (F.shiftedTangent a v u p) ^ 2 ∂ν| ≤ A ^ 2 * M := by
    apply F.toFieldSmoothFamily.affineLaw_integral_bound a v ζ p hV
      ((F.measurable_shiftedTangent a v p).pow_const 2) (sq_nonneg A)
    intro u
    rw [abs_pow]
    have h := pow_le_pow_left₀ (abs_nonneg _) (F.shiftedTangent_bound a v u hp hR hc) 2
    nlinarith
  have hsquare : |(∫ u, F.shiftedTangent a v u p ∂ν) ^ 2| ≤ (A * M) ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hiA 2
  unfold secondMean
  calc
    _ ≤ |∫ u, F.shiftedSecond a v u p ∂ν| +
        |ζ * ((∫ u, (F.shiftedTangent a v u p) ^ 2 ∂ν) -
          (∫ u, F.shiftedTangent a v u p ∂ν) ^ 2)| := abs_add_le _ _
    _ ≤ C * M + |ζ| * (A ^ 2 * M + (A * M) ^ 2) := by
      apply add_le_add hiC
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hiAA hsquare)) (abs_nonneg ζ)
    _ = F.secondMeanCap R D ζ V := by
      dsimp only [secondMeanCap, A, C, M]

end FieldSecondFamily
end InvariantIsing

end

end OAI
