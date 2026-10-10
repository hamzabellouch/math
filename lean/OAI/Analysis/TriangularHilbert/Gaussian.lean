import OAI.Analysis.TriangularHilbert.CubicProduct

namespace OAI

section

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TriangularHilbert.Heat

def density (σ t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t ^ 2 / (2 * σ))

def weight (h u p σ : ℝ) : ℝ := h * density σ (u - p)
def score (u p σ : ℝ) : ℝ := (u - p) / σ

theorem density_pos {σ : ℝ} (hσ : 0 < σ) (t : ℝ) : 0 < density σ t := by
  unfold density
  positivity

theorem density_nonneg {σ : ℝ} (_hσ : 0 ≤ σ) (t : ℝ) : 0 ≤ density σ t := by
  unfold density
  positivity

theorem density_eq_gaussianPDFReal {σ : ℝ} (hσ : 0 ≤ σ) :
    density σ = ProbabilityTheory.gaussianPDFReal 0 ⟨σ, hσ⟩ := by
  ext t
  change (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-t^2 / (2*σ)) =
    (Real.sqrt (2 * Real.pi * σ))⁻¹ * Real.exp (-(t-0)^2 / (2*σ))
  rw [sub_zero]

theorem density_integrable {σ : ℝ} (hσ : 0 ≤ σ) : Integrable (density σ) := by
  rw [density_eq_gaussianPDFReal hσ]
  exact ProbabilityTheory.integrable_gaussianPDFReal 0 _

theorem weight_hasDerivAt_center (h u p σ : ℝ) (_hσ : 0 < σ) :
    HasDerivAt (fun q => weight h u q σ) (score u p σ * weight h u p σ) p := by
  have hexp : HasDerivAt (fun q : ℝ => -(u - q)^2 / (2 * σ)) ((u - p) / σ) p := by
    convert! ((((hasDerivAt_const p u).sub (hasDerivAt_id p)).pow 2).neg.div_const
      (2 * σ)) using 1
    dsimp
    ring
  have ht := ((Real.hasDerivAt_exp _).comp p hexp).const_mul
    (h * (Real.sqrt (2 * Real.pi * σ))⁻¹)
  convert! ht using 1
  · ext q
    simp only [weight, density, Function.comp_apply]
    ring
  · simp only [score, weight, density]
    ring

theorem score_hasDerivAt_center (u p σ : ℝ) :
    HasDerivAt (fun q => score u q σ) (-σ⁻¹) p := by
  convert! ((hasDerivAt_const p u).sub (hasDerivAt_id p)).div_const σ using 1
  simp [div_eq_mul_inv]

theorem weight_score_hasDerivAt_center (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun q => score u q σ * weight h u q σ)
      ((score u p σ ^ 2 - σ⁻¹) * weight h u p σ) p := by
  convert! (score_hasDerivAt_center u p σ).mul (weight_hasDerivAt_center h u p σ hσ) using 1
  ring

theorem density_normalization_hasDerivAt (σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => (Real.sqrt (2 * Real.pi * s))⁻¹)
      (-((Real.sqrt (2 * Real.pi * σ))⁻¹) / (2 * σ)) σ := by
  have hpos : 0 < 2 * Real.pi * σ := by positivity
  have hspos : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.2 hpos
  have ht := ((Real.hasDerivAt_sqrt hpos.ne').comp σ
    ((hasDerivAt_id σ).const_mul (2 * Real.pi))).inv hspos.ne'
  convert! ht using 1
  dsimp
  field_simp
  nlinarith [Real.sq_sqrt hpos.le]

theorem weight_hasDerivAt_variance (h u p σ : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun s => weight h u p s)
      ((1 / 2 : ℝ) * (score u p σ ^ 2 - σ⁻¹) * weight h u p σ) σ := by
  have hexp : HasDerivAt (fun s : ℝ => -(u-p)^2 / (2*s))
      ((u-p)^2 / (2*σ^2)) σ := by
    convert! (hasDerivAt_const σ (-(u-p)^2)).div
      ((hasDerivAt_id σ).const_mul 2) (by positivity : 2*σ ≠ 0) using 1
    dsimp
    ring
  have ht := ((density_normalization_hasDerivAt σ hσ).mul
    ((Real.hasDerivAt_exp _).comp σ hexp)).const_mul h
  convert! ht using 1
  unfold score weight density
  dsimp
  field_simp
  ring

end TriangularHilbert.Heat
end
end

end OAI
