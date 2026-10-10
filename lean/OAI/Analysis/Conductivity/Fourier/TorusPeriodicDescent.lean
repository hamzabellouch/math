import Mathlib
import OAI.Analysis.Conductivity.Geometry.TorusDirectionalDerivative
import OAI.Analysis.Conductivity.Flux.TorusBoxFlux
import OAI.Analysis.Conductivity.Variational.FiniteEndPhysicalDescent

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
local instance torusPeriodicDescentMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusPeriodicDescentProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def torusPeriodicDescent (f : Coord3 → E) (z : ℝ × UnitAddTorus (Fin 2)) : E :=
  f ![z.1,2*Real.pi*torusRealRepresentative z.2 0,
    2*Real.pi*torusRealRepresentative z.2 1]

lemma torusAngles_scaled (t : ℝ) (x : Fin 2 → ℝ) :
    torusAngles ![t,2*Real.pi*x 0,2*Real.pi*x 1]=torusRealProjection x := by
  ext i
  fin_cases i <;> simp [torusAngles,torusRealProjection,Real.pi_ne_zero]

lemma torusPeriodicDescent_real {f : Coord3 → E}
    (hp : AngularPeriodic (2*Real.pi) f) (t : ℝ) (x : Fin 2 → ℝ) :
    torusPeriodicDescent f (t,torusRealProjection x)=f ![t,2*Real.pi*x 0,2*Real.pi*x 1] := by
  change f ![t,2*Real.pi*torusRealRepresentative (torusRealProjection x) 0,
    2*Real.pi*torusRealRepresentative (torusRealProjection x) 1]=_
  apply hp.eq_of_angles
  · rfl
  rw [torusAngles_scaled,torusAngles_scaled,torusRealProjection_representative]

lemma torusPeriodicDescent_angles {f : Coord3 → E}
    (hp : AngularPeriodic (2*Real.pi) f) (x : Coord3) :
    torusPeriodicDescent f (x 0,torusAngles x)=f x := by
  change f ![x 0,2*Real.pi*torusRealRepresentative (torusAngles x) 0,
    2*Real.pi*torusRealRepresentative (torusAngles x) 1]=_
  apply hp.eq_of_angles
  · rfl
  rw [torusAngles_scaled,torusRealProjection_representative]

lemma isOpenMap_torusRealProjection : IsOpenMap torusRealProjection := by
  change IsOpenMap (Pi.map (fun _ : Fin 2 => ((↑) : ℝ → UnitAddCircle)))
  exact IsOpenMap.piMap (fun _ => QuotientAddGroup.isOpenMap_coe)
    (Filter.Eventually.of_forall fun _ => QuotientAddGroup.mk_surjective)

lemma torusRealProjection_surjective : Function.Surjective torusRealProjection :=
  fun θ => ⟨torusRealRepresentative θ,torusRealProjection_representative θ⟩

lemma continuous_torusPeriodicDescent {f : Coord3 → E}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) :
    Continuous (torusPeriodicDescent f) := by
  let P := Prod.map (id : ℝ → ℝ) torusRealProjection
  have hP : IsQuotientMap P := (IsOpenMap.id.prodMap isOpenMap_torusRealProjection).isQuotientMap
    (continuous_id.prodMap continuous_torusRealProjection)
    (Function.surjective_id.prodMap torusRealProjection_surjective)
  apply hP.continuous_iff.mpr
  have he : torusPeriodicDescent f ∘ P =
      fun z : ℝ × (Fin 2 → ℝ) => f ![z.1,2*Real.pi*z.2 0,2*Real.pi*z.2 1] := by
    funext z
    exact torusPeriodicDescent_real hp z.1 z.2
  rw [he]
  exact hf.comp (by fun_prop)

lemma integral_unitTorus_iterated_general [CompleteSpace E]
    {F : UnitAddTorus (Fin 2) → E} (hF : Continuous F) :
    (∫ θ,F θ)=∫ θ : UnitAddCircle,∫ η : UnitAddCircle,F ![θ,η]
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have hc : Continuous (MeasurableEquiv.finTwoArrow.symm :
      UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) := by
    change Continuous (fun z : UnitAddCircle × UnitAddCircle => ![z.1,z.2])
    fun_prop
  rw [←(volume_preserving_finTwoArrow UnitAddCircle).symm.integral_comp']
  change (∫ z : UnitAddCircle × UnitAddCircle,F (MeasurableEquiv.finTwoArrow.symm z)
    ∂volume.prod volume)=_
  rw [integral_prod (fun z : UnitAddCircle × UnitAddCircle => F (MeasurableEquiv.finTwoArrow.symm z))
    ((hF.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

lemma integral_unitCircle_haar_interval {F : UnitAddCircle → E} :
    (∫ θ : UnitAddCircle,F θ ∂AddCircle.haarAddCircle)=∫ t in (0:ℝ)..1,F (t:UnitAddCircle) := by
  have h := (UnitAddCircle.intervalIntegral_preimage 0 F).symm
  simpa only [zero_add,unitCircle_volume_eq_haar] using h

lemma torusPeriodicDescent_integral {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) (t : ℝ) :
    (∫ θ,torusPeriodicDescent f (t,θ))=(2*Real.pi)⁻¹^2*torusCellIntegral (2*Real.pi) f t := by
  have hc : Continuous (fun θ => torusPeriodicDescent f (t,θ)) :=
    (continuous_torusPeriodicDescent hf hp).comp (continuous_const.prodMk continuous_id)
  rw [integral_unitTorus_iterated_general hc]
  rw [integral_unitCircle_haar_interval]
  have hπ : 2*Real.pi≠0 := by positivity
  have hi (x : ℝ) : (∫ θ : UnitAddCircle,torusPeriodicDescent f (t,![(x:UnitAddCircle),θ])
      ∂AddCircle.haarAddCircle)=
      (2*Real.pi)⁻¹*(∫ y in (0:ℝ)..(2*Real.pi),f ![t,2*Real.pi*x,y]) := by
    rw [integral_unitCircle_haar_interval]
    have he (y : ℝ) : torusPeriodicDescent f (t,![(x:UnitAddCircle),(y:UnitAddCircle)])=
        f ![t,2*Real.pi*x,2*Real.pi*y] := torusPeriodicDescent_real hp t ![x,y]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_mul_left (fun y => f ![t,2*Real.pi*x,y]) hπ]
    simp
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => ∫ y in (0:ℝ)..(2*Real.pi),f ![t,x,y]) hπ]
  simp only [mul_zero,mul_one,smul_eq_mul,torusCellIntegral]
  ring

end ScalarConductivity

end
end

end OAI
