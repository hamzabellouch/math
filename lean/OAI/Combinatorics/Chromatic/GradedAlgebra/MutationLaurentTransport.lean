import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedCutAction
import OAI.Combinatorics.Chromatic.Walls.HalfspaceLaurentTransport

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
noncomputable section
variable {K M I : Type*} [Field K] [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (pc : I) (pos : Bool)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def mutationTorusEquiv : Torus v Ω ≃+* Torus v Ω :=
  { Equiv.ofBijective (mutationTorusPush Ω hΩ C pc pos v : Torus v Ω → Torus v Ω)
      ⟨Finsupp.mapDomain_injective (mutationLinearPiece_injective Ω hΩ C pc pos),
       Finsupp.mapDomain_surjective (mutationLinearPiece_surjective Ω hΩ C pc pos)⟩ with
    map_mul' := (mutationTorusPush Ω hΩ C pc pos v).map_mul
    map_add' := (mutationTorusPush Ω hΩ C pc pos v).map_add }

end
end ElementaryPositivity.QuantumTorus
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [Fintype I] in
lemma mutationSideAction_embed [Fintype I] (pos : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos
      (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc)) f)=
    PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc))
      (PowerSeries.map (mutationTorusEquiv LaurentRay.vUnit Ω hΩ C pc pos).toRingHom f) := by
  cases pos
  · exact completedShearAction_embed LaurentRay.vUnit Ω hΩ _ _ _ f
  · simp only [mutationSideAction, ite_true, RingEquiv.refl_apply]
    apply PowerSeries.ext
    intro D
    simp only [coeff_map]
    congr 1
    change (coeff (R := Torus LaurentRay.vUnit Ω) D f)=Finsupp.mapDomain id (coeff (R := Torus LaurentRay.vUnit Ω) D f)
    exact (Finsupp.mapDomain_id).symm
lemma mutationSideAction_inverse_embed (pos : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    (mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos).symm
      (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc)) f)=
    PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (pureDegree_simple_self C coord hcoord pc))
      (PowerSeries.map (mutationTorusEquiv LaurentRay.vUnit Ω hΩ C pc pos).symm.toRingHom f) := by
  apply (mutationSideAction LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
    (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω) pos).injective
  rw [RingEquiv.apply_symm_apply,mutationSideAction_embed Ω hΩ C coord hcoord pc]
  congr 1
  apply PowerSeries.ext
  intro D
  simp only [coeff_map,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,RingEquiv.apply_symm_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

theorem pushedRationalTransport_laurent_lift {a b : Module.Dual ℝ E}
    (HA : RegularCovector C e a) (HB : RegularCovector C e b)
    (Hside : (0 < a (e (simpleRoot C pc)) ∧ 0 < b (e (simpleRoot C pc))) ∨
      (a (e (simpleRoot C pc)) < 0 ∧ b (e (simpleRoot C pc)) < 0))
    (f : PowerSeries (Torus LaurentRay.vUnit Ω)) :
    ∃g : PowerSeries (Torus LaurentRay.vUnit Ω),
      pushedRationalTransport Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg HA HB
        (PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
          (pureDegree_simple_self C coord hcoord pc)) f)=
      PowerSeries.map (embed LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (pureDegree_simple_self C coord hcoord pc)) g := by
  classical
  rw [pushedRationalTransport_apply]
  unfold covectorSideAction
  rw [mutationSideAction_inverse_embed Ω hΩ C coord hcoord pc]
  obtain ⟨g,hg⟩:=completedTransport_laurent_lift Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
    HA HB Hside (PowerSeries.map
      (mutationTorusEquiv LaurentRay.vUnit Ω hΩ C pc (decide (0 < a (e (simpleRoot C pc))))).symm.toRingHom f)
  rw [hg,mutationSideAction_embed Ω hΩ C coord hcoord pc]
  exact ⟨_,rfl⟩
end
end ElementaryPositivity.RationalFiber

end

end OAI
