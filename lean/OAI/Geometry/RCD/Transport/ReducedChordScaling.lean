import OAI.Geometry.RCD.Transport.RenyiIntegralAdditivity
import OAI.Geometry.RCD.Transport.ReducedDyadicChord

namespace OAI

/-! # Exact cancellation of a finite nonzero mass in the reduced bound -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem inverse_density_scaled_eval (μ : Measure X) [SigmaFinite μ]
    (π : Measure C(Time,X)) [IsFiniteMeasure π] {c : ℝ≥0∞} (hc : c ≠ ∞)
    (s : Time) (ha : π.map (fun γ => γ s) ≪ μ) (q : ℝ) :
    ∀ᵐ γ ∂π, (((c • π).map (fun γ => γ s)).rnDeriv μ (γ s))^q =
      c^q*((π.map (fun γ => γ s)).rnDeriv μ (γ s))^q := by
  rw [Measure.map_smul _ (measurable_path_eval s).aemeasurable]
  have he := Measure.rnDeriv_smul_left_of_ne_top (π.map (fun γ => γ s)) μ hc
  have ht := Measure.rnDeriv_lt_top (π.map (fun γ => γ s)) μ
  have hp := ae_of_ae_map (measurable_path_eval s).aemeasurable
    ((he.and ht).filter_mono ha.ae_le)
  filter_upwards [hp] with γ hγ
  rw [hγ.1]
  change (c*(π.map (fun γ => γ s)).rnDeriv μ (γ s))^q=_
  exact ENNReal.mul_rpow_of_ne_top hc hγ.2.ne q

theorem reduced_chord_of_smul (μ : Measure X) [SigmaFinite μ]
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (ha₀ : π.map (fun γ => γ 0) ≪ μ) (ha₁ : π.map (fun γ => γ 1) ≪ μ)
    {K N : ℝ} (hN : 1 < N) (t : Time)
    (h : ReducedRenyiChordBound μ K N (c • π) t) : ReducedRenyiChordBound μ K N π t := by
  let k := c^(1-1/N)
  have hk0 : k ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hc).ne'
  have hkt : k ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hc0 hc
  have hcq : c*c^(-(1/N))=k := by
    dsimp only [k]
    rw [show 1-1/N=1+(-(1/N)) by ring,ENNReal.rpow_add _ _ hc0 hc,ENNReal.rpow_one]
  let F := fun γ : C(Time,X) =>
    sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
      ((π.map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
    sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
      ((π.map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N))
  have hleft : (∫⁻ γ, sigma K (N+1) (1-(t:ℝ)) (dist (γ 0) (γ 1))*
      (((c • π).map (fun γ => γ 0)).rnDeriv μ (γ 0))^(-(1/N))+
      sigma K (N+1) (t:ℝ) (dist (γ 0) (γ 1))*
      (((c • π).map (fun γ => γ 1)).rnDeriv μ (γ 1))^(-(1/N)) ∂(c • π))=
      k*(∫⁻ γ, F γ ∂π) := by
    rw [lintegral_smul_measure]
    calc
      _ = c*(∫⁻ γ, c^(-(1/N))*F γ ∂π) := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards [inverse_density_scaled_eval μ π hc 0 ha₀ (-(1/N)),
          inverse_density_scaled_eval μ π hc 1 ha₁ (-(1/N))] with γ hγ₀ hγ₁
        rw [hγ₀,hγ₁]
        dsimp only [F]
        ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc0 hc),←mul_assoc,hcq]
  unfold ReducedRenyiChordBound at h ⊢
  rw [hleft,Measure.map_smul _ (measurable_path_eval t).aemeasurable,
    renyiIntegral_smul μ _ hc hN] at h
  change k*(∫⁻ γ, F γ ∂π) ≤ k*renyiIntegral μ (π.map (fun γ => γ t)) N at h
  calc
    _ = k⁻¹*(k*(∫⁻ γ, F γ ∂π)) := by rw [←mul_assoc,ENNReal.inv_mul_cancel hk0 hkt,one_mul]
    _ ≤ k⁻¹*(k*renyiIntegral μ (π.map (fun γ => γ t)) N) := mul_le_mul' le_rfl h
    _ = _ := by rw [←mul_assoc,ENNReal.inv_mul_cancel hk0 hkt,one_mul]

end RegularPointCoordinates

end

end OAI
