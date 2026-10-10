import Mathlib
import OAI.Analysis.Conductivity.Sources.AngularGraph
import OAI.Analysis.Conductivity.Geometry.CylinderPointEnergy

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance endPointEnergyMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance endPointEnergyIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sourceEndSmoothDensity (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (κ a b : ℝ) (φ : (Fin 3 → ℝ) → ℝ) (z : ℝ × UnitAddTorus (Fin 2)) : ℝ :=
  fullEndFlatCovector s f κ z.1 z.2 ⬝ᵥ
    (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (sourceAngularJet φ a b k.succ z).re))

lemma sourceEndSmoothDensity_cylinder (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ a b R : ℝ) (hR : 0≤R)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (sourceEndSmoothDensity s f κ a b φ) ((FiniteAxisMeasure R).prod volume) ∧
    (∫ z,sourceEndSmoothDensity s f κ a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (flatCylinderEnergy s (cylinderEndJet s hs κ R hR f)
        (sourceAngularLpJet hφ a b R)).re := by
  let u := cylinderEndJet s hs κ R hR f
  let v := sourceAngularLpJet hφ a b R
  have hv (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0 := by
    filter_upwards [sourceAngularLpJet_ae hφ a b R k.succ] with z hz
    change (sourceAngularLpJet hφ a b R k.succ z).im=0
    rw [hz]
    exact sourceAngularJet_im φ a b k.succ z
  obtain ⟨hi,he⟩ := flatCylinderEnergy_real_integral s u v hv
  have hve : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (v k.succ z).re)=
        (fun k : Fin 3 => (sourceAngularJet φ a b k.succ z).re) := by
    filter_upwards [ae_all_iff.mpr (fun k : Fin 3 => sourceAngularLpJet_ae hφ a b R k.succ)] with z hz
    exact funext (fun k => congrArg Complex.re (hz k))
  have hd : (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))=ᵐ[(FiniteAxisMeasure R).prod volume]
        sourceEndSmoothDensity s f κ a b φ := by
    filter_upwards [cylinderEndJet_covector_ae s hs κ R hR f,hve] with z hu hv
    change (fun k : Fin 3 => (cylinderEndJet s hs κ R hR f k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))=_
    rw [hu,hv]
    rfl
  exact ⟨hi.congr hd,(integral_congr_ae hd).symm.trans he.symm⟩

lemma sourceEndSmoothDensity_green (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ a b R : ℝ) (hR : 0<R)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ z,sourceEndSmoothDensity s f κ a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      inner ℝ (spectralGraphWeight (torusRate s) f)
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s b hφ))-
      κ*spectralGraphMean (torusRate s) (smoothCollarTrace s b hφ)+
      cylinderTerminalFlux s κ R f (smoothCollarTrace s (a*R+b) hφ) := by
  rw [(sourceEndSmoothDensity_cylinder s hs f κ a b R hR.le hφ).2]
  exact cylinderEndJet_real_green s hs κ hR f
    ⟨(_,(_,_)),sourceAngularLpJet_graph s hφ a b R⟩

end ScalarConductivity

end
end

end OAI
