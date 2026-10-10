import Mathlib
import OAI.Combinatorics.Chromatic.Walls.InfinityCutCharts

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance infinityLineRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance infinityLineAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance infinityLineAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def mutatedLineFactorPositive (a : ℝ) : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a,
    mutatedLineFactor_constant Ω hΩ C coord pc e he L hdeg v k H a,
    mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a⟩

def actualInfinityLineUnit (a : ℝ) : (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
    (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)

lemma actualInfinityLine_nocut (a : ℝ)
    (hp : (k+a • v) (e (simpleRoot C pc))≠0)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<(k+a • v) (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<(k+a • v) (e (simpleRoot C pc))))
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) x) := by
  classical
  let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
  have hs:=cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp
  unfold actualLineLetter
  split
  · next ha=>
    simp only
    let data:=lineRayData C e he L hdeg v k H a ha
    let F:=chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)
    let G:=mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
    have hf:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hG : G.val=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (orientPowerSeries (decide (v (e data.root)<0)) F.val) := by
      simp only [G,mutatedLineFactorPositive,mutatedLineFactor,dite_eq_left ha,ite_eq_right hp]
      rfl
    have hbf:=simple_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hbi:=simple_inverse_regrade_bound C coord hcoord Ω pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    exact mutation_infinity_oriented_square Ω hΩ C coord hcoord pc pos
      (decide (v (e data.root)<0)) F hf hbf hbi G hG x
  · next ha=>
    have hg : (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a).val=1 := by
      simp only [mutatedLineFactorPositive,mutatedLineFactor,dite_eq_right ha]
    have hu:=infinityCompletedUnit_one Ω C coord hcoord pc LaurentRay.vUnit _ hg
    change innerHom _ _=infinitySideHom _ _ _ _ _ _ (innerHom _ x)
    rw [show actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a=1 from hu,
      innerHom_one]
    have h1 : boundedRationalUnit LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        1 (RegradeBound.one _ _ _ _) (RegradeBound.one _ _ _ _)=1 := by
      apply Units.ext
      exact rationalRegrade_one _ _ _ _ _ _ _ _
    rw [h1,innerHom_one]
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance infinityLineCutRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance infinityLineCutAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance infinityLineCutAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma actualInfinityLine_cut_unit (a : ℝ)
    (hp : (k+a • v) (e (simpleRoot C pc))=0) :
    actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a=
      if decide (v (e (simpleRoot C pc))<0) then
        (completedPureUnit LaurentRay.vUnit Ω hΩ (-simpleRoot C pc))⁻¹
      else completedPureUnit LaurentRay.vUnit Ω hΩ (-simpleRoot C pc) := by
  classical
  have ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k :=
    ⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
  let P : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
    ⟨normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc),
      normalizedSimple_constant Ω _,by
        rw [←simpleDatum_value Ω (mutatedRoots Ω C pc) pc]
        exact WallUnitDatum.graded Ω _ (fun _=>True) _ (simpleDatum_allowed _ pc)⟩
  have hP : P.val=raySeries LaurentRay.vUnit Ω (-simpleRoot C pc) (shiftedElementary LaurentRay.vUnit 0) := by
    rw [laurent_shiftedElementary_zero]
    change normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)=_
    rw [mutatedRoot_p]
    rfl
  have hU:=infinityCompletedUnit_pure Ω C coord hcoord pc LaurentRay.vUnit hΩ P hP
  let G:=mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a
  have hG : G.val=orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0))) P.val := by
    simp only [G,mutatedLineFactorPositive,mutatedLineFactor,dite_eq_left ha,ite_eq_left hp,P]
  cases hb : decide (v (e (simpleRoot C pc))<0)
  · simp only [Bool.false_eq_true,ite_false]
    change infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G=_
    rw [show G=P from Subtype.ext (by simpa only [hb,Bool.not_false,orientPowerSeries,ite_true] using hG)]
    exact hU
  · simp only [ite_true]
    change infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit G=_
    rw [infinityCompletedUnit_inverse Ω C coord hcoord pc LaurentRay.vUnit P G
      (by simpa only [hb,Bool.not_true,orientPowerSeries,Bool.false_eq_true,ite_false] using hG),hU]

include hdeg H in
lemma line_cut_offset_ne : k (e (simpleRoot C pc))≠0 := by
  have hr : e (simpleRoot C pc)∈realRootsThrough e C 1 := by
    exact realRoot_mem e C 1 1 le_rfl (simpleRoot C pc) (simpleRoot_degree C pc)
  apply (H 1).avoid _ hr
  rw [Submodule.span_singleton_eq_bot.mpr rfl,Submodule.mem_bot]
  intro hz
  have HH:=hdeg 1 (simpleRoot C pc) (simpleRoot_degree C pc)
  rw [hz,map_zero] at HH
  norm_num at HH

include hdeg H in
lemma line_cut_direction_ne (a : ℝ) (hp : (k+a • v) (e (simpleRoot C pc))=0) :
    v (e (simpleRoot C pc))≠0 := by
  intro hz
  have hp' : k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0:=hp
  rw [hz,mul_zero,add_zero] at hp'
  exact line_cut_offset_ne C pc e L hdeg v k H hp'
lemma actualInfinityLine_square (a : ℝ)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (AffineCut.beforeSide (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (AffineCut.afterSide (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a)
      (comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a) x) := by
  classical
  by_cases hp : (k+a • v) (e (simpleRoot C pc))=0
  · have hs:=AffineCut.sides_at_zero (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a hp
    rw [hs.1,hs.2,actualInfinityLine_cut_unit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a hp]
    have ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k :=
      ⟨1,line_cut_event C pc e L hdeg v k H a hp⟩
    have hv:=line_cut_direction_ne C pc e L hdeg v k H a hp
    have hq : ∀n : ℕ,1-(↑(LaurentRay.vUnit^(-2:ℤ)):LaurentSeries ℚ)^(n+1)≠0 := by
      intro n
      rw [LaurentRay.vUnit_zpow]
      exact UnitSelections.laurent_q_not_root n
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    by_cases hn : v (e (simpleRoot C pc))<0
    · have hn' : ¬0<v (e (simpleRoot C pc)):=not_lt_of_ge hn.le
      simp only [hn,hn',decide_true,decide_false,ite_true,comparisonAction]
      exact infinitySide_cut LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) hq x
    · have hn' : 0<v (e (simpleRoot C pc)):=lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hv)
      simp only [hn,hn',decide_true,decide_false,Bool.false_eq_true,ite_false,comparisonAction]
      exact infinitySide_cut_reverse LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) hq x
  · have hs:=AffineCut.sides_eq_of_ne (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) a hp
    rw [hs.1,hs.2]
    exact actualInfinityLine_nocut Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a hp x
end
end ElementaryPositivity.RationalFiber

end

end OAI
