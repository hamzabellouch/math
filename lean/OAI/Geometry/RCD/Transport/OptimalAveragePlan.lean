import OAI.Geometry.RCD.Transport.OptimalCommonContactSet
import OAI.Analysis.RCDHeat.KantorovichRadius

namespace OAI

/-! # A common optimal plan dominating two prescribed optimizers -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem optimalPlan_average {ν₀ ν₁ : Measure X}
    (π ρ : Measure C(Time,X)) [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hgπ : ∀ᵐ γ ∂π, IsGeodesic γ) (hgρ : ∀ᵐ γ ∂ρ, IsGeodesic γ)
    (hpπ : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hpρ : IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0,γ 1)))) :
    ∃ τ : Measure C(Time,X), IsProbabilityMeasure τ ∧
      (∀ᵐ γ ∂τ, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (τ.map (fun γ => (γ 0,γ 1))) ∧ π ≪ τ ∧ ρ ≪ τ := by
  let c : ℝ≥0∞ := ENNReal.ofReal (1/2)
  have hc0 : c≠0 := by norm_num [c]
  have hcc : c+c=1 := by
    dsimp only [c]
    rw [←ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  let τ := c • π+c • ρ
  have hπac : π ≪ τ := (Measure.absolutelyContinuous_smul hc0).trans
    (show c • π≤τ from Measure.le_add_right le_rfl).absolutelyContinuous
  have hρac : ρ ≪ τ := (Measure.absolutelyContinuous_smul hc0).trans
    (show c • ρ≤τ from Measure.le_add_left le_rfl).absolutelyContinuous
  have hτ : IsProbabilityMeasure τ := ⟨by
    change c*π univ+c*ρ univ=1
    simp only [measure_univ,mul_one,hcc]⟩
  have hm : Measurable (fun γ : C(Time,X) => (γ 0,γ 1)) :=
    (measurable_path_eval 0).prodMk (measurable_path_eval 1)
  have hmap : τ.map (fun γ => (γ 0,γ 1))=
      c • π.map (fun γ => (γ 0,γ 1))+c • ρ.map (fun γ => (γ 0,γ 1)) := by
    dsimp only [τ]
    rw [Measure.map_add _ _ hm,Measure.map_smul _ hm.aemeasurable,Measure.map_smul _ hm.aemeasurable]
  have heq (ν : Measure X) : c • ν+c • ν=ν := by rw [←add_smul,hcc,one_smul]
  have hp : IsOptimalCoupling ν₀ ν₁ (τ.map (fun γ => (γ 0,γ 1))) := by
    rw [hmap]
    refine ⟨?_,?_,?_⟩
    · rw [Measure.map_add _ _ measurable_fst,Measure.map_smul _ measurable_fst.aemeasurable,
        Measure.map_smul _ measurable_fst.aemeasurable,hpπ.1,hpρ.1,heq]
    · rw [Measure.map_add _ _ measurable_snd,Measure.map_smul _ measurable_snd.aemeasurable,
        Measure.map_smul _ measurable_snd.aemeasurable,hpπ.2.1,hpρ.2.1,heq]
    · intro η hη0 hη1
      rw [transportCost_add,transportCost_smul,transportCost_smul]
      calc
        _ ≤ c*transportCost η+c*transportCost η :=
          add_le_add (mul_le_mul' le_rfl (hpπ.2.2 η hη0 hη1))
            (mul_le_mul' le_rfl (hpρ.2.2 η hη0 hη1))
        _ = _ := by rw [←add_mul,hcc,one_mul]
  refine ⟨τ,hτ,?_,hp,hπac,hρac⟩
  apply ae_add_measure_iff.mpr
  exact ⟨hgπ.filter_mono Measure.smul_absolutelyContinuous.ae_le,
    hgρ.filter_mono Measure.smul_absolutelyContinuous.ae_le⟩

end RegularPointCoordinates

end

end OAI
