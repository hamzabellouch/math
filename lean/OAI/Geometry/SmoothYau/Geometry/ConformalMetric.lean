import Mathlib
import OAI.Geometry.SmoothYau.Model

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def conformalMetric (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) : SmoothMetric E M where
  inner x := (b x) ^ 2 • g.inner x
  symm x v w := by change (b x) ^ 2 * g.inner x v w = (b x) ^ 2 * g.inner x w v; rw [g.symm]
  pos x v hv := mul_pos (sq_pos_of_pos (hpos x)) (g.pos x v hv)
  isVonNBounded x := by
    apply ((g.isVonNBounded x).image ((b x)⁻¹ •
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) x))).subset
    intro v hv
    refine ⟨b x • v, ?_, ?_⟩
    · change (b x) ^ 2 * g.inner x v v < 1 at hv
      simpa only [Set.mem_ofPred_eq, map_smul, _root_.smul_apply,
        smul_eq_mul, pow_two, mul_assoc] using hv
    · simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
      exact inv_smul_smul₀ (ne_of_gt (hpos x)) v
  contMDiff := (hb.pow 2).smul_section g.contMDiff

lemma conformalMetric_coefficients (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    metricCoefficients (conformalMetric g b hb hpos) p y =
      (b ((chartAt E p).symm y)) ^ 2 • metricCoefficients g p y := rfl

lemma real_matrix_inv_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Matrix ι ι ℝ) {c : ℝ} (hc : c ≠ 0) : (c • a)⁻¹ = c⁻¹ • a⁻¹ := by
  by_cases ha : IsUnit a.det
  · let : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul a c ha, invOf_eq_inv]
  · have hz : a.det = 0 := by simpa only [isUnit_iff_ne_zero, not_not] using ha
    have hz' : ¬IsUnit (c • a).det := by simp [hz]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ ha, Matrix.nonsing_inv_apply_not_isUnit _ hz', smul_zero]

lemma conformalMetric_inverse (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    (metricCoefficients (conformalMetric g b hb hpos) p y)⁻¹ =
      ((b ((chartAt E p).symm y)) ^ 2)⁻¹ • (metricCoefficients g p y)⁻¹ := by
  rw [conformalMetric_coefficients, real_matrix_inv_smul _ (pow_ne_zero 2 (ne_of_gt (hpos _)))]

lemma conformalMetric_density_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (p : M) (y : E) :
    Real.sqrt (Matrix.det (metricCoefficients (conformalMetric g b hb hpos) p y)) =
      (b ((chartAt E p).symm y)) ^ 3 * Real.sqrt (Matrix.det (metricCoefficients g p y)) := by
  rw [conformalMetric_coefficients, Matrix.det_smul]
  simp only [Fintype.card_fin, CoordIndex, hd]
  rw [show ((b ((chartAt E p).symm y)) ^ 2) ^ 3 = ((b ((chartAt E p).symm y)) ^ 3) ^ 2 by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (hpos _).le _)]

def weightedLaplacian (g : SmoothMetric E M) (b u : M → ℝ) (x : M) : ℝ :=
  let c := chartAt E x
  let a := metricCoefficients g x
  let ρ := fun y => Real.sqrt (Matrix.det (a y))
  (ρ (c x))⁻¹ * ∑ i, fderiv ℝ
    (fun y => b (c.symm y) * (ρ y * ∑ j, (a y)⁻¹ i j *
      fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)))
    (c x) (Module.finBasis ℝ E i)

lemma conformalMetric_laplacian_three (hd : Module.finrank ℝ E = 3)
    (g : SmoothMetric E M) (b : M → ℝ)
    (hb : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ b) (hpos : ∀ x, 0 < b x) (u : M → ℝ) (x : M) :
    laplaceBeltrami (conformalMetric g b hb hpos) u x =
      (b x ^ 3)⁻¹ * weightedLaplacian g b u x := by
  let c := chartAt E x
  have hx : c.symm (c x) = x := c.left_inv (mem_chart_source E x)
  have hflux : ∀ i, (fun y => Real.sqrt (Matrix.det (metricCoefficients (conformalMetric g b hb hpos) x y)) *
      ∑ j, (metricCoefficients (conformalMetric g b hb hpos) x y)⁻¹ i j *
        fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j)) =
      (fun y => b (c.symm y) * (Real.sqrt (Matrix.det (metricCoefficients g x y)) *
      ∑ j, (metricCoefficients g x y)⁻¹ i j * fderiv ℝ (u ∘ c.symm) y (Module.finBasis ℝ E j))) := by
    intro i
    funext y
    rw [conformalMetric_density_three hd, conformalMetric_inverse]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    have hn := ne_of_gt (hpos (c.symm y))
    dsimp only [c] at hn ⊢
    field_simp [hn]
  dsimp only [c] at hflux hx
  unfold laplaceBeltrami weightedLaplacian
  dsimp only
  simp only [hflux]
  rw [conformalMetric_density_three hd, hx, mul_inv_rev]
  ring

end YauCounterexamples


end

end OAI
