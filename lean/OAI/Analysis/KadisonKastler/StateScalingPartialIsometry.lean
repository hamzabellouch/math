import OAI.Analysis.KadisonKastler.StateScalingAlgebra
import OAI.Analysis.FactorGeneration.DyadicComparison

namespace OAI

/-! # Centralizer supports of state-scaling partial isometries -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

def stateCentralizerProjection (p : AlgebraProjection M)
    (hc : ProductStateCentralizes M Ω p.val.val) :
    AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω) := by
  refine ⟨⟨p.val.val,⟨p.val.property,hc⟩⟩,?_,?_⟩
  · exact Subtype.ext (congrArg (fun a : Algebra M => a.val) p.property.isIdempotentElem.eq)
  · exact Subtype.ext (congrArg (fun a : Algebra M => a.val) p.property.isSelfAdjoint.star_eq)

def stateCentralizerInclusion (Ω : H) :
    Algebra (stateCentralizerVonNeumann (M := M) Ω) →⋆ₐ[ℂ] Algebra M :=
  StarSubalgebra.inclusion (stateCentralizerVonNeumann_le Ω)

def includeCentralizerProjection
    (p : AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω)) :
    AlgebraProjection M :=
  ⟨stateCentralizerInclusion Ω p.val,p.property.map (stateCentralizerInclusion Ω)⟩

def includeCentralizerPartialIsometry
    (v : PartialIsometry (stateCentralizerVonNeumann (M := M) Ω)) :
    PartialIsometry M where
  support := includeCentralizerProjection v.support
  val := stateCentralizerInclusion Ω v.val
  initial := by
    change star (stateCentralizerInclusion Ω v.val)*stateCentralizerInclusion Ω v.val =
      stateCentralizerInclusion Ω v.support.val
    simpa only [map_mul,map_star] using congrArg (stateCentralizerInclusion Ω) v.initial

theorem includeCentralizerPartialIsometry_target
    (v : PartialIsometry (stateCentralizerVonNeumann (M := M) Ω)) :
    (includeCentralizerPartialIsometry v).target=includeCentralizerProjection v.target := by
  apply Subtype.ext
  change stateCentralizerInclusion Ω v.val * star (stateCentralizerInclusion Ω v.val) =
    stateCentralizerInclusion Ω (v.val*star v.val)
  simp only [map_mul,map_star]

theorem partialIsometry_compose_target_of_eq (v w : PartialIsometry M)
    (h : w.target=v.support) :
    (v.compose w (le_of_eq h)).target=v.target := by
  apply Subtype.ext
  rw [PartialIsometry.compose_target,h,v.mul_support]
  rfl

theorem stateScales_compose {r s : ℝ} (v w : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (hw : StateScales M Ω s w.val.val)
    (h : w.target ≤ v.support) :
    StateScales M Ω (r*s) (v.compose w h).val.val :=
  hv.mul hw v.val.property w.val.property

theorem includeCentralizerPartialIsometry_scales
    (v : PartialIsometry (stateCentralizerVonNeumann (M := M) Ω)) :
    StateScales M Ω 1 (includeCentralizerPartialIsometry v).val.val :=
  StateScales.of_centralizer v.val

def scalingSupport {r : ℝ} (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (hr : r ≠ 0) :
    AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω) :=
  stateCentralizerProjection v.support (by
    have hh := hv.initial_centralizes v.val.property hr
    have he : star v.val.val*v.val.val=v.support.val.val := congrArg Subtype.val v.initial
    rwa [he] at hh)

def scalingTarget {r : ℝ} (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (hr : r ≠ 0) :
    AlgebraProjection (stateCentralizerVonNeumann (M := M) Ω) :=
  stateCentralizerProjection v.target (hv.final_centralizes v.val.property hr)

theorem scalingSupport_trace {r : ℝ} (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (hr : r ≠ 0)
    (hunit : ‖Ω‖=1) (hsep : Function.Injective (algebraVectorMap M Ω)) :
    (stateCentralizerTrace Ω hunit hsep).trace (scalingSupport v hv hr).val =
      (r : ℂ)*(stateCentralizerTrace Ω hunit hsep).trace (scalingTarget v hv hr).val := by
  have hh := hv.initial_state v.val.property
  have he : star v.val.val*v.val.val=v.support.val.val := congrArg Subtype.val v.initial
  rw [he] at hh
  exact hh

/-- Restrict the final projection of a partial isometry. -/
def cutPartialIsometryTarget (v : PartialIsometry M) (p : AlgebraProjection M)
    (hp : p ≤ v.target) : PartialIsometry M :=
  (v.adjoint.compose (PartialIsometry.onProjection p) (by
    rw [PartialIsometry.onProjection_target]
    exact hp)).adjoint

theorem cutPartialIsometryTarget_val (v : PartialIsometry M) (p : AlgebraProjection M)
    (hp : p ≤ v.target) : (cutPartialIsometryTarget v p hp).val=p.val*v.val := by
  change star (star v.val*p.val)=p.val*v.val
  rw [star_mul,star_star,p.property.isSelfAdjoint.star_eq]

theorem cutPartialIsometryTarget_target (v : PartialIsometry M) (p : AlgebraProjection M)
    (hp : p ≤ v.target) : (cutPartialIsometryTarget v p hp).target=p := by
  apply Subtype.ext
  change star (star v.val*p.val)*star (star (star v.val*p.val))=p.val
  rw [star_star]
  have hh := (v.adjoint.compose (PartialIsometry.onProjection p) (by
    rw [PartialIsometry.onProjection_target]
    exact hp)).initial
  exact hh

theorem cutPartialIsometryTarget_scales {r : ℝ} (v : PartialIsometry M)
    (hv : StateScales M Ω r v.val.val) (p : AlgebraProjection M) (hp : p ≤ v.target)
    (hc : ProductStateCentralizes M Ω p.val.val) :
    StateScales M Ω r (cutPartialIsometryTarget v p hp).val.val := by
  rw [cutPartialIsometryTarget_val]
  have hh := (StateScales.of_centralizer (stateCentralizerProjection p hc).val).mul
    hv p.val.property v.val.property
  change StateScales M Ω (1*r) (p.val.val*v.val.val) at hh
  change StateScales M Ω r (p.val.val*v.val.val)
  simpa only [one_mul] using hh

end

end KadisonKastler

end OAI
