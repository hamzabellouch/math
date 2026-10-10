import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.InfinityLaurentFinite
import OAI.Combinatorics.Chromatic.GradedAlgebra.PurePolynomialCoefficients

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries HahnSeries PowerSeriesAdjoint WallUnits
noncomputable section
lemma constantCoeff_inner_const_inv {A:Type*} [Ring A] (u:Aˣ) (f:PowerSeries A) :
    constantCoeff (innerHom (Units.map (PowerSeries.C (R:=A)) u)⁻¹ f)=
      innerHom u⁻¹ (constantCoeff f) := by
  change constantCoeff (PowerSeries.C u.inv*f*PowerSeries.C u.val)=u.inv*constantCoeff f*u.val
  rw [map_mul,map_mul,constantCoeff_C,constantCoeff_C]

variable {M:Type*} [AddCommGroup M]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)
local instance finitePureMutationRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance finitePureMutationAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance finitePureMutationAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
local instance finitePureMutationNonUnitalSemiring : NonUnitalSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalSemiring
local instance finitePureMutationNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toNonUnitalNonAssocSemiring

lemma expandFiberInfinity_lattice (F:Torus LaurentRay.vUnit Ω) :
    expandFiberInfinity LaurentRay.vUnit Ω hΩ k p (embed LaurentRay.vUnit Ω hΩ k p hp F)=
      latticeHahn LaurentRay.vUnit Ω (-k) F := by
  apply HahnSeries.ext
  funext j
  apply Finsupp.ext
  intro m
  rw [expandFiberInfinity_embed_coeff LaurentRay.vUnit Ω hΩ k p hp,latticeHahn_coeff]
  rfl

lemma pureLaurentUnit_actual_val (q:M) :
    (pureLaurentUnit LaurentRay.vUnit Ω hΩ q).val=
      ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (normalizedSimple Ω q) := by
  change purePower LaurentRay.vUnit Ω hΩ q (shiftedElementary LaurentRay.vUnit 0)=_
  rw [purePower_eq,laurent_shiftedElementary_zero]
  rfl
lemma pureLaurentUnit_actual_inv (q:M) :
    ((pureLaurentUnit LaurentRay.vUnit Ω hΩ q)⁻¹).val=
      ofPowerSeries ℤ (Torus LaurentRay.vUnit Ω) (invOfUnit (normalizedSimple Ω q) 1) := by
  change purePower LaurentRay.vUnit Ω hΩ q (shiftedElementary LaurentRay.vUnit 0)⁻¹=_
  rw [purePower_eq,laurent_shiftedElementary_zero,normalizedSimple_inverse Ω hΩ]

lemma inner_pure_hahn (q:M) (x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)) :
    innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ q) x=hahnAction (normalizedSimple Ω q) x := by
  change (pureLaurentUnit LaurentRay.vUnit Ω hΩ q).val*x*((pureLaurentUnit LaurentRay.vUnit Ω hΩ q)⁻¹).val=_
  rw [pureLaurentUnit_actual_val,pureLaurentUnit_actual_inv]
  rfl

lemma expand_opposite_inverse_actual
    (f:FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)) :
    expandFiberInfinity LaurentRay.vUnit Ω hΩ k p
      (oppositeInverseActionHom LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω) f)=
      innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ (-p))⁻¹
        (expandFiberInfinity LaurentRay.vUnit Ω hΩ k p f) := by
  have hq:∀n:ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0:=by
    intro n
    rw [LaurentRay.vUnit_zpow]
    exact UnitSelections.laurent_q_not_root n
  have H:=completed_expand_opposite_inverse LaurentRay.vUnit Ω hΩ k p hq (PowerSeries.C f)
  rw [completedOppositeInverseAction_eq,PowerSeries.map_C,PowerSeries.map_C] at H
  have H0:=congrArg constantCoeff H
  rw [constantCoeff_C,completedPureUnit,constantCoeff_inner_const_inv,PowerSeries.map_C,constantCoeff_C] at H0
  exact H0

include hΩ in
lemma finite_cut_hahn (F F':Torus LaurentRay.vUnit Ω)
    (hF:embed LaurentRay.vUnit Ω hΩ k p hp F=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F')) :
    hahnAction (normalizedSimple Ω (-p))
      (latticeHahn LaurentRay.vUnit Ω (-k)
        (Torus.push LaurentRay.vUnit Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) F))=
      latticeHahn LaurentRay.vUnit Ω (-k) F' := by
  have HC:=congrArg (fun g:FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω) →+*
      FiberTorus LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)=>
        g (embed LaurentRay.vUnit Ω hΩ k p hp F'))
      (rational_cut_identity LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω))
  change shearActionHom LaurentRay.vUnit _ _
      (pureAction LaurentRay.vUnit _ _ (embed LaurentRay.vUnit Ω hΩ k p hp F'))=
      oppositeInverseActionHom LaurentRay.vUnit _ _ (embed LaurentRay.vUnit Ω hΩ k p hp F') at HC
  rw [←hF,shearAction_embed LaurentRay.vUnit Ω hΩ k p hp F] at HC
  have HE:=expand_opposite_inverse_actual Ω hΩ k p (embed LaurentRay.vUnit Ω hΩ k p hp F')
  rw [←HC] at HE
  have HH:=congrArg (innerHom (pureLaurentUnit LaurentRay.vUnit Ω hΩ (-p))) HE
  rw [innerHom_cancel_inv,inner_pure_hahn,expandFiberInfinity_lattice Ω hΩ k p hp,
    expandFiberInfinity_lattice Ω hΩ k p hp] at HH
  exact HH

include hΩ in
lemma finite_cut_actual (τ:M →+ ℤ) (hτ:τ (-p)=1) (F F':Torus LaurentRay.vUnit Ω)
    (hF:embed LaurentRay.vUnit Ω hΩ k p hp F=
      pureAction LaurentRay.vUnit (complementOmega k Ω) (complementAlpha k p Ω)
        (embed LaurentRay.vUnit Ω hΩ k p hp F')) (m:M) :
    actualPolynomialAdjointCoefficient Ω τ (normalizedSimple Ω (-p))
      (Torus.push LaurentRay.vUnit Ω Ω (mutationShear Ω p) (mutationShear_pairing Ω hΩ p) F) m=F' m := by
  have HH:=congrArg (fun x:HahnSeries ℤ (Torus LaurentRay.vUnit Ω)=>x.coeff ((-k) m) m)
    (finite_cut_hahn Ω hΩ k p hp F F' hF)
  rw [hahnAction_actual_coeff Ω hΩ,latticeHahn_coeff,ite_eq_left rfl] at HH
  rw [actual_pure_order_independent Ω hΩ τ (-k) (-p) hτ (by simp [hp])]
  exact HH
end
end ElementaryPositivity.RationalFiber

end

end OAI
