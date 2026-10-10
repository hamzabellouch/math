import OAI.Geometry.RCD.Transport.PairedPathUniqueness
import OAI.Geometry.RCD.Transport.PairedSuffixUniqueness

namespace OAI

/-! # Explicit optimal half mixtures with their compression and domination -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SeparableSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [SeparableSpace X] in
theorem half_mixture_plan_data {ν₀ ν₁ : Measure X}
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1)))) :
    let τ := (2:ℝ≥0∞)⁻¹ • (π+ρ)
    IsProbabilityMeasure τ ∧ (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (τ.map (fun γ => (γ 0,γ 1))) ∧
      (2:ℝ≥0∞)⁻¹ • π ≤ τ ∧ (2:ℝ≥0∞)⁻¹ • ρ ≤ τ := by
  let c : ℝ≥0∞ := (2:ℝ≥0∞)⁻¹
  let τ := c • (π+ρ)
  have hcc : c+c=1 := by
    dsimp only [c]
    rw [←two_mul,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  have hprob : IsProbabilityMeasure τ := ⟨by
    change c*(π univ+ρ univ)=1
    simp only [measure_univ,mul_add,mul_one,hcc]⟩
  have hm := (measurable_path_eval (X:=X) 0).prodMk (measurable_path_eval 1)
  have he (ν : Measure X) : c • (ν+ν)=ν := half_smul_self ν
  have hopt : IsOptimalCoupling ν₀ ν₁ (τ.map (fun γ => (γ 0,γ 1))) := by
    rw [show τ=c • (π+ρ) from rfl,Measure.map_smul _ hm.aemeasurable,Measure.map_add _ _ hm]
    refine ⟨?_,?_,?_⟩
    · rw [Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_add _ _ measurable_fst,
        hpπ.1,hpρ.1,he]
    · rw [Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_add _ _ measurable_snd,
        hpπ.2.1,hpρ.2.1,he]
    · intro η hη₀ hη₁
      rw [transportCost_smul,transportCost_add,mul_add]
      calc
        _ ≤ c*transportCost η+c*transportCost η :=
          add_le_add (mul_le_mul' le_rfl (hpπ.2.2 η hη₀ hη₁))
            (mul_le_mul' le_rfl (hpρ.2.2 η hη₀ hη₁))
        _ = _ := by rw [←add_mul,hcc,one_mul]
  refine ⟨hprob,?_,hopt,?_,?_⟩
  · exact ((ae_add_measure_iff.mpr ⟨hgπ,hgρ⟩).filter_mono Measure.smul_absolutelyContinuous.ae_le)
  · exact smul_le_smul_left c (Measure.le_add_right le_rfl)
  · exact smul_le_smul_left c (Measure.le_add_left le_rfl)

omit [SeparableSpace X] in
theorem half_mixture_compression (μ : Measure X) (π ρ : Measure C(Time,X))
    {C : ℝ≥0∞} (hπ : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hρ : ∀ t : Time, ρ.map (fun γ => γ t) ≤ C • μ) (t : Time) :
    ((2:ℝ≥0∞)⁻¹ • (π+ρ)).map (fun γ => γ t) ≤ C • μ := by
  rw [half_mixture_map_eval]
  exact (_root_.smul_le_smul_left ((2:ℝ≥0∞)⁻¹) (add_le_add (hπ t) (hρ t))).trans_eq (half_smul_self _)

end RegularPointCoordinates

end

end OAI
