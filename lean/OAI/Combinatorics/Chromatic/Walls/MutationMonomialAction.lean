import Mathlib
import OAI.Combinatorics.Chromatic.Walls.MutationRegradeCompatibility
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootCoefficients
import OAI.Combinatorics.Chromatic.QuantumTorus.NormalizedMonomialAction
import OAI.Combinatorics.Chromatic.Walls.MutatedLineCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint WallUnits
noncomputable section
variable {M I:Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I) (pos:Bool)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma mutationCompletion_monomialConjugate (b:M) (f:PowerSeries (Torus LaurentRay.vUnit Ω)) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (monomialConjugate LaurentRay.vUnit Ω b f)=
      monomialConjugate LaurentRay.vUnit Ω (mutationLinearPiece Ω C pc pos b)
        (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) := by
  unfold mutationCompletion
  rw [regrade_monomialConjugate LaurentRay.vUnit Ω hΩ]
  simp only [monomialConjugate,map_mul,PowerSeries.map_C,mutationTorusPush,Torus.push_X,map_neg]

lemma mutationCompletion_normalizedMonomialAction (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b:M)
    (hf:RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hc:constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (normalizedMonomialAction LaurentRay.vUnit Ω f b)=
      normalizedMonomialAction LaurentRay.vUnit Ω (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f)
        (mutationLinearPiece Ω C pc pos b) := by
  rw [normalizedMonomialAction,mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hf
    (monomialConjugate_regradeBound LaurentRay.vUnit Ω hΩ b _ _ (hf.invOfUnit _ _ _ _)),
    mutationCompletion_monomialConjugate,mutationCompletion_inverse Ω hΩ C coord pc pos f hf hc]
  rfl

lemma mutationCompletion_actualRootCoefficient (f:PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f)
    (hg:FullHomogeneous LaurentRay.vUnit Ω (rootOrder coord) f) (m:M) :
    actualRootCoefficient LaurentRay.vUnit Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) (mutationLinearPiece Ω C pc pos m)=
      actualRootCoefficient LaurentRay.vUnit Ω (rootOrder coord) f m := by
  calc
    _ = actualRootCoefficient LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
        (regrade LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f) m := by
      unfold actualRootCoefficient mutationCompletion
      change (if 0 ≤ mutationNewOrder Ω C coord pc pos m then _ else _) = _
      split_ifs
      · rw [coeff_map,mutationTorusPush_read]
        rfl
      · rfl
    _ = _ := regrade_actualRootCoefficient LaurentRay.vUnit Ω (rootOrder coord)
      (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f hf hg m

def actualMonomialAdjointCoefficient (τ:M →+ ℤ) (f:PowerSeries (Torus LaurentRay.vUnit Ω)) (b m:M) :
    LaurentSeries ℚ :=
  actualRootCoefficient LaurentRay.vUnit Ω τ (normalizedMonomialAction LaurentRay.vUnit Ω f b) (m-b)*
    (↑(LaurentRay.vUnit^(Ω (m-b) b)):LaurentSeries ℚ)

include hcoord in
lemma mutation_actualMonomialAdjointCoefficient (f:CompletedPositive LaurentRay.vUnit Ω C)
    (hf:RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1) f.val)
    (b m:M) :
    actualMonomialAdjointCoefficient Ω (rootOrder (mutatedCoordinates Ω C coord pc))
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val)
      (mutationLinearPiece Ω C pc pos b) (mutationLinearPiece Ω C pc pos m)=
    actualMonomialAdjointCoefficient Ω (rootOrder coord) f.val b m := by
  let N:CompletedPositive LaurentRay.vUnit Ω C:=
    ⟨normalizedMonomialAction LaurentRay.vUnit Ω f.val b,
      normalizedMonomialAction_constant LaurentRay.vUnit Ω hΩ f.val b f.property.1,
      normalizedMonomialAction_graded LaurentRay.vUnit Ω hΩ C f b⟩
  have H:=mutationCompletion_actualRootCoefficient Ω hΩ C coord pc pos N.val
    (normalizedMonomialAction_bound LaurentRay.vUnit Ω hΩ _ _ f.val b hf)
    (completed_full_homogeneous LaurentRay.vUnit Ω C coord hcoord N) (m-b)
  rw [mutationCompletion_normalizedMonomialAction Ω hΩ C coord pc pos f.val b hf f.property.1] at H
  unfold actualMonomialAdjointCoefficient
  rw [←map_sub,mutationLinearPiece_pairing Ω hΩ C pc pos,H]
end
end ElementaryPositivity.QuantumTorus

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

include he hdeg H in
lemma actualLineLetter_old (a : ℝ)
    (ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k) :
    ∃r d,0<d ∧ HasRootDegree C d r ∧ v (e r)≠0 ∧
      (∀N,RayGeneric C N r ((k+a • v).toAddMonoidHom.comp e)) ∧
      comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)=
      if v (e r)<0 then completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C))
      else (completedBiUnit LaurentRay.vUnit Ω C coord hcoord pc
        (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)))⁻¹ := by
  classical
  let data:=lineRayData C e he L hdeg v k H a ha
  by_cases hp : (k+a • v) (e (simpleRoot C pc))=0
  · have Hrp : OnPositiveRay data.root (simpleRoot C pc):=
      (data.generic 1).2 1 one_pos le_rfl (simpleRoot C pc) (simpleRoot_degree C pc) hp
    have HG : ∀N,RayGeneric C N (simpleRoot C pc) ((k+a • v).toAddMonoidHom.comp e):=by
      intro N
      exact ⟨hp,fun n hn hnN m hm hm0=>Hrp.symm.trans ((data.generic N).2 n hn hnN m hm hm0)⟩
    have HV : v (e (simpleRoot C pc))≠0:=by
      intro hz
      have hk : k (e (simpleRoot C pc))=0:=by
        change k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 at hp
        simpa only [hz,mul_zero,add_zero] using hp
      exact section_offset_generic C e L hdeg 1 v k (H 1) 1 one_pos le_rfl
        (simpleRoot C pc) (simpleRoot_degree C pc) hk
    refine ⟨simpleRoot C pc,1,one_pos,simpleRoot_degree C pc,HV,HG,?_⟩
    have HU:=completedBiUnit_pure Ω hΩ C coord hcoord pc ((k+a • v).toAddMonoidHom.comp e) HG
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_left hp]
    rw [HU]
    by_cases hn : v (e (simpleRoot C pc))<0
    · simp only [hn,decide_true,ite_eq_left,comparisonOld]
    · simp only [hn,decide_false,comparisonOld,↓reduceIte]
  · refine ⟨data.root,data.degree,data.degree_pos,data.root_degree,data.transverse,data.generic,?_⟩
    unfold actualLineLetter
    simp only [dite_eq_left ha,dite_eq_right hp]
    change comparisonOld _ _ _ _ _ _ _ _ _
      (orientedBounded _ _ _ _ _ _ _ _ (decide (v (e data.root)<0)))=_
    by_cases hn : v (e data.root)<0
    · simp only [hn,decide_true,orientedBounded,↓reduceIte,comparisonOld]
    · simp only [hn,decide_false,orientedBounded,Bool.false_eq_true,↓reduceIte,comparisonOld]
end
end ElementaryPositivity.RationalFiber

end

end OAI
