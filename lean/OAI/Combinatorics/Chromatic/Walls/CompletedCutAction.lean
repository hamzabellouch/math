import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedPathIndependence
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalShearEmbedding

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
lemma shearRatio_inv_val_add (t u : ℤ) : (↑((shearRatio v (t+u))⁻¹):RatFunc K)=
    (↑((shearRatio v t)⁻¹):RatFunc K)*scale (v^(-2*t)) (↑((shearRatio v u)⁻¹):RatFunc K) := by
  simp only [Units.val_inv_eq_inv_val,shearRatio_val_add,map_inv₀,mul_inv_rev]
  exact mul_comm _ _
def shearActionInvHom : FiberTorus v Ω α →+* FiberTorus v Ω α :=
  FiberTorus.gauge v Ω α (fun t=>(↑((shearRatio v t)⁻¹):RatFunc K)) (by simp)
    (shearRatio_inv_val_add v)
lemma shearAction_cancel (f : FiberTorus v Ω α) :
    shearActionHom v Ω α (shearActionInvHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa only [←Units.val_mul,inv_mul_cancel,Units.val_one] using
    FiberTorus.gaugeAdd_trivial v Ω α f
lemma shearActionInv_cancel (f : FiberTorus v Ω α) :
    shearActionInvHom v Ω α (shearActionHom v Ω α f)=f := by
  change FiberTorus.gaugeAdd v Ω α _ (FiberTorus.gaugeAdd v Ω α _ f)=_
  rw [FiberTorus.gauge_comp]
  simpa only [←Units.val_mul,mul_inv_cancel,Units.val_one] using
    FiberTorus.gaugeAdd_trivial v Ω α f
def shearAction : FiberTorus v Ω α ≃+* FiberTorus v Ω α :=
  RingEquiv.ofRingHom (shearActionHom v Ω α) (shearActionInvHom v Ω α)
    (RingHom.ext (shearAction_cancel v Ω α)) (RingHom.ext (shearActionInv_cancel v Ω α))
def completedShearAction : PowerSeries (FiberTorus v Ω α) ≃+* PowerSeries (FiberTorus v Ω α) :=
  RingEquiv.ofRingHom (PowerSeries.map (shearAction v Ω α).toRingHom)
    (PowerSeries.map (shearAction v Ω α).symm.toRingHom)
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])
    (by apply RingHom.ext; intro f; ext n; simp [PowerSeries.coeff_map])

def completedOppositeInverseAction : PowerSeries (FiberTorus v Ω α) ≃+*
    PowerSeries (FiberTorus v Ω α) :=
  (completedPureAction v Ω α).trans (completedShearAction v Ω α)

lemma completed_cut_identity (f : PowerSeries (FiberTorus v Ω α)) :
    completedShearAction v Ω α (completedPureAction v Ω α f)=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f := by
  apply PowerSeries.ext
  intro D
  change coeff D (PowerSeries.map (shearActionHom v Ω α)
    (PowerSeries.map (pureActionHom v Ω α) f))=_
  simp only [coeff_map]
  exact congrArg (fun F : FiberTorus v Ω α →+* FiberTorus v Ω α=>F (coeff D f))
    (rational_cut_identity v Ω α)

lemma completedOppositeInverseAction_eq (f : PowerSeries (FiberTorus v Ω α)) :
    completedOppositeInverseAction v Ω α f=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f :=
  completed_cut_identity v Ω α f

include v in
lemma completedShearAction_embed (hΩ : ∀m,Ω m m=0) (k : M →+ ℤ) (p : M) (hp : k p=1)
    (f : PowerSeries (Torus v Ω)) :
    completedShearAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (PowerSeries.map (embed v Ω hΩ k p hp) f)=
    PowerSeries.map (embed v Ω hΩ k p hp)
      (PowerSeries.map (Torus.push v Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p)) f) := by
  apply PowerSeries.ext
  intro D
  change coeff D (PowerSeries.map (shearActionHom v (complementOmega k Ω) (complementAlpha k p Ω))
    (PowerSeries.map (embed v Ω hΩ k p hp) f))=_
  simp only [coeff_map]
  exact shearAction_embed v Ω hΩ k p hp (coeff D f)
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (α : M →+ ℤ)
def mutationSideAction (pos : Bool) : PowerSeries (FiberTorus v Ω α) ≃+*
    PowerSeries (FiberTorus v Ω α) :=
  if pos then RingEquiv.refl _ else completedShearAction v Ω α

lemma mutationSideAction_cut (f : PowerSeries (FiberTorus v Ω α)) :
    mutationSideAction v Ω α false (completedPureAction v Ω α
      ((mutationSideAction v Ω α true).symm f))=
      PowerSeries.map (oppositeInverseActionHom v Ω α) f := by
  exact completed_cut_identity v Ω α f

lemma mutationSideAction_cut_reverse (f : PowerSeries (FiberTorus v Ω α)) :
    mutationSideAction v Ω α true ((completedPureAction v Ω α).symm
      ((mutationSideAction v Ω α false).symm f))=
      (completedOppositeInverseAction v Ω α).symm f := by
  rfl

lemma mutationSideAction_inner (pos : Bool) (u : (PowerSeries (FiberTorus v Ω α))ˣ)
    (f : PowerSeries (FiberTorus v Ω α)) :
    mutationSideAction v Ω α pos (innerHom u ((mutationSideAction v Ω α pos).symm f))=
      innerHom (Units.map (mutationSideAction v Ω α pos).toMonoidHom u) f := by
  rw [show mutationSideAction v Ω α pos (innerHom u ((mutationSideAction v Ω α pos).symm f))=
    (mutationSideAction v Ω α pos).toRingHom (innerHom u ((mutationSideAction v Ω α pos).symm f)) from rfl]
  rw [map_innerHom]
  simp only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,RingEquiv.apply_symm_apply]
  rfl
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def covectorSideAction (a : Module.Dual ℝ E) :
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) ≃+*
    PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)) :=
  mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
    (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω)
    (decide (0<a (e (simpleRoot C pc))))

def pushedRationalTransport {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) :=
  ((covectorSideAction Ω C coord pc e a).symm.trans
    (completedTransportEquiv Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB)).trans
    (covectorSideAction Ω C coord pc e b)

lemma pushedRationalTransport_apply {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB f=
      covectorSideAction Ω C coord pc e b
        (completedTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
          ((covectorSideAction Ω C coord pc e a).symm f)) := rfl

lemma pushedRationalTransport_self {a : Module.Dual ℝ E}
    (HA : RegularCovector C e a)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HA f=f := by
  rw [pushedRationalTransport_apply,completedTransport_self,RingEquiv.apply_symm_apply]

lemma pushedRationalTransport_trans {a b c : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b) (HC : RegularCovector C e c)
    (f : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HC f=
      pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HB HC
        (pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB f) := by
  simp only [pushedRationalTransport_apply,RingEquiv.symm_apply_apply]
  rw [completedTransport_trans]
end
end ElementaryPositivity.RationalFiber

end

end OAI
