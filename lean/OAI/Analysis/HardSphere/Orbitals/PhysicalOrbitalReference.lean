import Mathlib
import OAI.Analysis.HardSphere.Comparison.PhysicalAffinity

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def orbitalObservationEquiv : ((Y×X)×X)≃ᵐ(X×X×Y) where
  toFun p := (p.1.2,p.2,p.1.1)
  invFun p := ((p.2.2,p.1),p.2.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (Y×X)×X ↦ (p.1.2,p.2,p.1.1)); fun_prop
  measurable_invFun := by change Measurable (fun p : X×X×Y ↦ ((p.2.2,p.1),p.2.1)); fun_prop

def tagBathSwapEquiv : ((X×Y)×X)≃ᵐ((Y×X)×X) where
  toFun p := ((p.1.2,p.1.1),p.2)
  invFun p := ((p.1.2,p.1.1),p.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (X×Y)×X ↦ ((p.1.2,p.1.1),p.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.2,p.1.1),p.2)); fun_prop

def orbitalSwapEquiv : ((Y×X)×X)≃ᵐ((Y×X)×X) where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2)); fun_prop
  measurable_invFun := by change Measurable (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2)); fun_prop

lemma tagBathSwap_preserving (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] :
    MeasurePreserving (tagBathSwapEquiv (X:=X) (Y:=Y)) ((μ.prod ν).prod μ) ((ν.prod μ).prod μ) :=
  (Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).prod (MeasurePreserving.id μ)

lemma physical_unrestricted_affinity {n : ℕ} (μ : Measure X) (ν : Measure (Fin n→X))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : (Fin n→X)×X→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (ν.prod μ))
    (hf0 : ∀p,0 ≤ f p) :
    let P := ((μ.prod ν).withDensity (fun p ↦ ENNReal.ofReal (f (p.2,p.1)^2))).prod μ
    measureAffinity (P.map (cellObservation true)) (P.map (cellObservation false))=
      ∫Y,(∫x,f (Y,x) ∂μ)^2 ∂ν := by
  dsimp only
  let P := ((μ.prod ν).withDensity (fun p ↦ ENNReal.ofReal (f (p.2,p.1)^2))).prod μ
  let ξ := (ν.prod μ).prod μ
  let g₁ := fun p : ((Fin n→X)×X)×X ↦ ENNReal.ofReal (f p.1^2)
  let g₂ := fun p : ((Fin n→X)×X)×X ↦ ENNReal.ofReal (f (p.1.1,p.2)^2)
  have hg₁ : Measurable g₁ := ((hfm.comp measurable_fst).pow_const 2).ennreal_ofReal
  have hg₂ : Measurable g₂ := ((hfm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).pow_const 2).ennreal_ofReal
  have hD : P.map tagBathSwapEquiv=ξ.withDensity g₁ := by
    dsimp only [P]
    have hρ : Measurable (fun p : X×(Fin n→X) ↦ ENNReal.ofReal (f (p.2,p.1)^2)) := by fun_prop
    rw [prod_withDensity_left hρ]
    change (((μ.prod ν).prod μ).withDensity (g₁∘tagBathSwapEquiv)).map tagBathSwapEquiv=ξ.withDensity g₁
    rw [map_density_comp _ _ tagBathSwapEquiv.measurable g₁ hg₁,(tagBathSwap_preserving μ ν).map_eq]
  have hS : (ξ.withDensity g₁).map orbitalSwapEquiv=ξ.withDensity g₂ := by
    change (ξ.withDensity (g₂∘orbitalSwapEquiv)).map orbitalSwapEquiv=ξ.withDensity g₂
    rw [map_density_comp _ _ orbitalSwapEquiv.measurable g₂ hg₂]
    change ((ξ.map (fun p ↦ ((p.1.1,p.2),p.1.2))).withDensity g₂)=_
    rw [(swapLast_preserving μ ν).map_eq]
  have he₁ : P.map (cellObservation true)=(ξ.withDensity g₁).map orbitalObservationEquiv := by
    rw [←hD,Measure.map_map orbitalObservationEquiv.measurable tagBathSwapEquiv.measurable]
    rfl
  have he₂ : P.map (cellObservation false)=(ξ.withDensity g₂).map orbitalObservationEquiv := by
    rw [←hS,←hD,Measure.map_map orbitalSwapEquiv.measurable tagBathSwapEquiv.measurable,
      Measure.map_map orbitalObservationEquiv.measurable (orbitalSwapEquiv.measurable.comp tagBathSwapEquiv.measurable)]
    rfl
  have hi₁ : Integrable (fun p : ((Fin n→X)×X)×X ↦ f p.1^2) ξ :=
    (memLp_two_iff_integrable_sq (hf.comp_fst μ).aestronglyMeasurable).1 (hf.comp_fst μ)
  have hi₂ : Integrable (fun p : ((Fin n→X)×X)×X ↦ f (p.1.1,p.2)^2) ξ := by
    have h := (hf.comp_fst μ).comp_measurePreserving (swapLast_preserving μ ν)
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  have : IsFiniteMeasure (ξ.withDensity g₁) := isFiniteMeasure_withDensity_ofReal hi₁.2
  have : IsFiniteMeasure (ξ.withDensity g₂) := isFiniteMeasure_withDensity_ofReal hi₂.2
  change measureAffinity (P.map _) (P.map _)=_
  rw [he₁,he₂,measureAffinity_map_equiv]
  simpa only [one_mul] using full_affinity_square μ ν f hf hf0 1 (by norm_num)

end HardSphere.Comparison
end
end

end OAI
