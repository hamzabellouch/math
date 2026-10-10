import OAI.Probability.InvariantIsing.Fields.FieldFiniteShiftData

namespace OAI

/-! Uniform mark-polynomial bounds for joint height derivatives. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

lemma shiftedTangent_bound (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) :
    |F.shiftedTangent a v i u p| ≤ (F.KP + F.KX * R) * (1 + |u|) := by
  have hP := F.kp_nonneg
  have hX := F.kx_nonneg
  unfold shiftedTangent
  calc
    _ ≤ |F.P i _| + |F.X _ * (fieldFiniteSlope a v p.1 i * u)| := abs_add_le _ _
    _ ≤ F.KP + F.KX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bP i _ hp
      · exact F.bX _ hp
    _ ≤ _ := by nlinarith [mul_nonneg hP (abs_nonneg u), mul_nonneg hX hR]

lemma shiftedMixed_bound (a : ℝ) (v : Fin n → ℝ) (i : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R : ℝ} (hR : 0 ≤ R)
    (hc : |fieldFiniteSlope a v p.1 i| ≤ R) :
    |F.shiftedMixed a v i u p| ≤ (F.KPX + F.KXX * R) * (1 + |u|) := by
  have hP := F.kpx_nonneg
  have hX := F.kxx_nonneg
  unfold shiftedMixed
  calc
    _ ≤ |F.PX i _| + |F.XX _ * (fieldFiniteSlope a v p.1 i * u)| := abs_add_le _ _
    _ ≤ F.KPX + F.KXX * (R * |u|) := by
      rw [abs_mul, abs_mul]
      gcongr
      · exact F.bPX i _ hp
      · exact F.bXX _ hp
    _ ≤ _ := by nlinarith [mul_nonneg hP (abs_nonneg u), mul_nonneg hX hR]

lemma shiftedHessian_bound (a : ℝ) (v : Fin n → ℝ) (i j : Fin n) (u : ℝ)
    {p : FieldCovariate n} (hp : p.1 ∈ I) {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hci : |fieldFiniteSlope a v p.1 i| ≤ R)
    (hcj : |fieldFiniteSlope a v p.1 j| ≤ R)
    (hd : |fieldFiniteCurvature a v p.1 i j| ≤ D) :
    |F.shiftedHessian a v i j u p| ≤
      (F.KPP + 2 * F.KPX * R + F.KXX * R ^ 2 + F.KX * D) * (1 + |u|) ^ 2 := by
  have hPP := F.kpp_nonneg
  have hPX := F.kpx_nonneg
  have hXX := F.kxx_nonneg
  have hX := F.kx_nonneg
  have h1 : 1 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  have hu : |u| ≤ (1 + |u|) ^ 2 := by nlinarith [sq_nonneg |u|, abs_nonneg u]
  have hu2 : |u| ^ 2 ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  let w := F.shiftPoint a v u p
  have hbPP := F.bPP i j w hp
  have hbPi := F.bPX i w hp
  have hbPj := F.bPX j w hp
  have hbXX := F.bXX w hp
  have hbX := F.bX w hp
  unfold shiftedHessian
  calc
    _ ≤ |F.PP i j w| + |F.PX i w * (fieldFiniteSlope a v p.1 j * u)| +
        |F.PX j w * (fieldFiniteSlope a v p.1 i * u)| +
        |F.XX w * (fieldFiniteSlope a v p.1 i * u) * (fieldFiniteSlope a v p.1 j * u)| +
        |F.X w * (fieldFiniteCurvature a v p.1 i j * u)| := by
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ F.KPP + F.KPX * (R * |u|) + F.KPX * (R * |u|) +
        F.KXX * (R * |u|) * (R * |u|) + F.KX * (D * |u|) := by
      simp only [abs_mul]
      gcongr
    _ = F.KPP * 1 + (2 * F.KPX * R) * |u| +
        (F.KXX * R ^ 2) * |u| ^ 2 + (F.KX * D) * |u| := by ring
    _ ≤ F.KPP * (1 + |u|) ^ 2 + (2 * F.KPX * R) * (1 + |u|) ^ 2 +
        (F.KXX * R ^ 2) * (1 + |u|) ^ 2 + (F.KX * D) * (1 + |u|) ^ 2 := by
      gcongr
    _ = _ := by ring

end FieldFiniteFamily
end InvariantIsing

end

end OAI
