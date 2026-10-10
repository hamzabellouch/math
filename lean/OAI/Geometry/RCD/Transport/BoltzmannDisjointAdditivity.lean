import OAI.Geometry.RCD.Transport.RenyiDisjointAdditivity
import OAI.Geometry.RCD.Coordinates.NormalizedHeatEntropy

namespace OAI

/-! # Exact Boltzmann entropy of disjoint finite components -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

theorem entropy_density_add_mutuallySingular (ν₀ ν₁ : Measure X)
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (hs : ν₀ ⟂ₘ ν₁) :
    (fun x => ((ν₀+ν₁).rnDeriv μ x).toReal * Real.log ((ν₀+ν₁).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal +
        (ν₁.rnDeriv μ x).toReal * Real.log (ν₁.rnDeriv μ x).toReal := by
  filter_upwards [Measure.rnDeriv_add ν₀ ν₁ μ,rnDeriv_disjoint_ae μ ν₀ ν₁ hs]
    with x hx hd
  rw [hx]
  rcases hd with hd | hd <;> simp [Pi.add_apply,hd]

theorem boltzmannEntropy_add_mutuallySingular (ν₀ ν₁ : Measure X)
    [IsFiniteMeasure ν₀] [IsFiniteMeasure ν₁] (hs : ν₀ ⟂ₘ ν₁)
    (h₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (h₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal * Real.log (ν₁.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ (ν₀+ν₁)=boltzmannEntropy μ ν₀+boltzmannEntropy μ ν₁ := by
  unfold boltzmannEntropy
  rw [integral_congr_ae (entropy_density_add_mutuallySingular μ ν₀ ν₁ hs),
    integral_add h₀ h₁]

theorem entropy_density_smul (ν : Measure X) [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c≠∞) :
    (fun x => ((c • ν).rnDeriv μ x).toReal * Real.log ((c • ν).rnDeriv μ x).toReal)
      =ᵐ[μ] fun x => (c.toReal*(ν.rnDeriv μ x).toReal) *
        Real.log (c.toReal*(ν.rnDeriv μ x).toReal) := by
  filter_upwards [Measure.rnDeriv_smul_left_of_ne_top ν μ hc] with x hx
  rw [hx]
  simp only [Pi.smul_apply,smul_eq_mul,ENNReal.toReal_mul]

theorem boltzmannEntropy_smul (ν : Measure X) [IsFiniteMeasure ν]
    {c : ℝ≥0∞} (hc : c≠∞) (hc0 : c≠0)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ (c • ν)=c.toReal*boltzmannEntropy μ ν+
      (c.toReal*Real.log c.toReal)*(∫ x, (ν.rnDeriv μ x).toReal ∂μ) := by
  unfold boltzmannEntropy
  rw [integral_congr_ae (entropy_density_smul μ ν hc)]
  exact integral_entropy_mul μ (ENNReal.toReal_pos hc0 hc)
    (.of_forall fun _ => ENNReal.toReal_nonneg) Measure.integrable_toReal_rnDeriv he

theorem boltzmannEntropy_smul_probability (ν : Measure X) [IsProbabilityMeasure ν]
    (ha : ν ≪ μ) {c : ℝ≥0∞} (hc : c≠∞) (hc0 : c≠0)
    (he : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ (c • ν)=c.toReal*boltzmannEntropy μ ν+c.toReal*Real.log c.toReal := by
  rw [boltzmannEntropy_smul μ ν hc hc0 he,Measure.integral_toReal_rnDeriv ha]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one]

theorem boltzmannEntropy_half_mixture (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    (ha₀ : ν₀ ≪ μ) (ha₁ : ν₁ ≪ μ) (hs : ν₀ ⟂ₘ ν₁)
    (h₀ : Integrable (fun x => (ν₀.rnDeriv μ x).toReal * Real.log (ν₀.rnDeriv μ x).toReal) μ)
    (h₁ : Integrable (fun x => (ν₁.rnDeriv μ x).toReal * Real.log (ν₁.rnDeriv μ x).toReal) μ) :
    boltzmannEntropy μ ((2:ℝ≥0∞)⁻¹ • (ν₀+ν₁))=
      (boltzmannEntropy μ ν₀+boltzmannEntropy μ ν₁)/2-Real.log 2 := by
  have hi : Integrable (fun x => ((ν₀+ν₁).rnDeriv μ x).toReal *
      Real.log ((ν₀+ν₁).rnDeriv μ x).toReal) μ :=
    (h₀.add h₁).congr (entropy_density_add_mutuallySingular μ ν₀ ν₁ hs).symm
  rw [boltzmannEntropy_smul μ (ν₀+ν₁) (by norm_num) (by norm_num) hi,
    boltzmannEntropy_add_mutuallySingular μ ν₀ ν₁ hs h₀ h₁,
    Measure.integral_toReal_rnDeriv (ha₀.add_left ha₁)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofNat,Real.log_inv]
  norm_num [Measure.real]
  ring

end RegularPointCoordinates

end

end OAI
