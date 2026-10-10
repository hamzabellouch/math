import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutatedPureFace
import OAI.Combinatorics.Chromatic.Walls.InfinityLine

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (C:(I → ℤ) →+ M) (coord:M →+ (I → ℤ)) (hcoord:∀d,coord (C d)=d) (pc:I)
variable (e:M →+ E) (he:Function.Injective e)
variable (S:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS:∀x,S x x=0)
variable (hcomp:∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k:Module.Dual ℝ E) (H:∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance mutatedPureLineRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedPureLineAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPureLineAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

include hcoord in
lemma pureFaceSeries_product {J:Type*} (l:List J) (f:J → PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf:∀a∈l,SeriesGraded LaurentRay.vUnit Ω C (f a)) :
    pureFaceSeries Ω coord pc (l.map f).prod=(l.map (fun a=>pureFaceSeries Ω coord pc (f a))).prod := by
  induction l with
  | nil=>exact pureFaceSeries_one Ω coord pc
  | cons a l ih=>
    simp only [List.map_cons,List.prod_cons]
    rw [pureFaceSeries_mul Ω C coord hcoord pc _ _ (hf a (by simp))
      (SeriesGraded.list_prod Ω C l f (fun a ha=>hf a (by simp [ha]))),
      ih (fun a ha=>hf a (by simp [ha]))]

include hcoord hS hcomp in
lemma mutatedLineProduct_pure (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k) (N:ℕ) (hN:1≤N) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  classical
  rw [mutatedLineProduct,pureFaceSeries_product Ω (mutatedRoots Ω C pc)
    (mutatedCoordinates Ω C coord pc) (mutatedCoordinates_retraction Ω C coord hcoord pc) pc _ _
    (fun a _=>mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a)]
  have heq:(fun a=>pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a))=
    (fun a=>if k (e (simpleRoot C pc))+a*v (e (simpleRoot C pc))=0 then
      orientPowerSeries (!(decide (v (e (simpleRoot C pc))<0)))
        (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc)) else 1):=by
    funext a
    simpa only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using
      mutatedLineFactor_pure Ω C coord hcoord pc hΩ e he S hS hcomp L hdeg v k H a
  rw [heq]
  apply pureCut_telescope _ (normalizedSimple_constant Ω _)
    (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc))) lo hi hlohi
    (Or.inl (RationalFiber.line_cut_offset_ne C pc e L hdeg v k H))
  · exact fun hz=>hlo (RationalFiber.line_cut_event C pc e L hdeg v k H lo hz)
  · exact fun hz=>hhi (RationalFiber.line_cut_event C pc e L hdeg v k H hi hz)
  · exact fun a ha=>(Finset.mem_filter.mp ha).2
  · intro a hla hah hz
    exact Finset.mem_filter.mpr ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
      (RationalFiber.line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩

include hcoord hS hcomp in
lemma mutatedLineCompletion_pure (lo hi:ℝ) (hlohi:lo<hi)
    (hlo:lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi:hi∉lineEvents (realRootsThrough e C 1) v k) :
    pureFaceSeries Ω (mutatedCoordinates Ω C coord pc) pc
      (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)*
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+lo • v) (e (simpleRoot C pc))))=
      pureCutGauge (normalizedSimple Ω (simpleRoot (mutatedRoots Ω C pc) pc))
        (decide (0<(k+hi • v) (e (simpleRoot C pc)))) := by
  apply PowerSeries.ext
  intro d
  let N:=max 1 ((mutationSize Ω C pc+1)*d)
  have HH:=mutatedLineProduct_pure Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H
    lo hi hlohi hlo hhi N (le_max_left _ _)
  rw [←HH]
  apply FormalLog.mul_coeff_congr
  · intro j hj
    rw [coeff_pureFaceSeries,coeff_pureFaceSeries,
      mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi j N
        (le_max_left _ _) ((Nat.mul_le_mul_left _ hj).trans (le_max_right _ _))]
  · exact fun _ _=>rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries RationalFiber
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
variable (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
variable (v : (LaurentSeries ℚ)ˣ)
local instance mutatedPureLineProductRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance mutatedPureLineProductAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance mutatedPureLineProductAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def completedProduct (l : List (CompletedPositive v Ω C)) : CompletedPositive v Ω C :=
  l.foldr (completedMul v Ω C) (completedOne v Ω C)

omit [DecidableEq I] in
lemma completedProduct_val (l : List (CompletedPositive v Ω C)) :
    (completedProduct Ω C v l).val=(l.map (fun F=>F.val)).prod := by
  induction l with
  | nil=>rfl
  | cons a l ih=>exact congrArg (fun x=>a.val*x) ih

lemma infinityCompletedUnit_product (l : List (CompletedPositive v Ω (mutatedRoots Ω C pc))) :
    infinityCompletedUnit Ω C coord hcoord pc v (completedProduct Ω (mutatedRoots Ω C pc) v l)=
      (l.map (infinityCompletedUnit Ω C coord hcoord pc v)).prod := by
  induction l with
  | nil=>exact infinityCompletedUnit_one Ω C coord hcoord pc v _ rfl
  | cons a l ih=>
    rw [List.map_cons,List.prod_cons,←ih]
    exact infinityCompletedUnit_mul Ω C coord hcoord pc v _ _ _ rfl
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
local instance mutatedPureLineFiberRing : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance mutatedPureLineFiberAddCommMonoid : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance mutatedPureLineFiberAddGroup : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def actualInfinityLineProductUnit (lo hi : ℝ) (N : ℕ) :
    (PowerSeries (HahnSeries ℤ (Torus LaurentRay.vUnit Ω)))ˣ :=
  ((intervalEventList C e v k lo hi N).map
    (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H)).prod

def mutatedLineProductPositive (lo hi : ℝ) (N : ℕ) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N,
    mutatedLineProduct_constant Ω hΩ C coord pc e he L hdeg v k H lo hi N,
    mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N⟩

lemma actualInfinityLineProductUnit_eq (lo hi : ℝ) (N : ℕ) :
    actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N=
      infinityCompletedUnit Ω C coord hcoord pc LaurentRay.vUnit
        (mutatedLineProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) := by
  let l:=(intervalEventList C e v k lo hi N).map
    (mutatedLineFactorPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H)
  have heq : mutatedLineProductPositive Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N=
      completedProduct Ω (mutatedRoots Ω C pc) LaurentRay.vUnit l := by
    apply Subtype.ext
    rw [completedProduct_val]
    simp only [l,List.map_map,Function.comp_def]
    rfl
  rw [heq,infinityCompletedUnit_product]
  simp only [l,List.map_map,Function.comp_def]
  rfl

lemma actualInfinityLine_product_square (lo hi : ℝ) (hlohi : lo<hi)
    (hlo : lo∉lineEvents (realRootsThrough e C 1) v k)
    (hhi : hi∉lineEvents (realRootsThrough e C 1) v k) (N : ℕ) (hN : 1≤N)
    (x : PowerSeries (FiberTorus LaurentRay.vUnit (complementOmega (pureDegree coord pc) Ω)
      (complementAlpha (pureDegree coord pc) (simpleRoot C pc) Ω))) :
    innerHom (actualInfinityLineProductUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N)
      (infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
        (decide (0<(k+lo • v) (e (simpleRoot C pc)))) x)=
    infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc)
      (decide (0<(k+hi • v) (e (simpleRoot C pc))))
      (comparisonWordAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineWord Ω C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi N) x) := by
  classical
  have hl : (k+lo • v) (e (simpleRoot C pc))≠0 :=
    fun hh=>hlo (line_cut_event C pc e L hdeg v k H lo hh)
  have hh : (k+hi • v) (e (simpleRoot C pc))≠0 :=
    fun hz=>hhi (line_cut_event C pc e L hdeg v k H hi hz)
  have HT:=AffineCut.telescope_sort (k (e (simpleRoot C pc))) (v (e (simpleRoot C pc)))
    (Or.inl (line_cut_offset_ne C pc e L hdeg v k H))
    (fun a=>comparisonAction LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
      (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
      (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a))
    (fun a=>innerHom (actualInfinityLineUnit Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a))
    (fun pos=>infinitySideHom LaurentRay.vUnit Ω hΩ (pureDegree coord pc) (simpleRoot C pc) pos)
    (intervalLineEvents C e v k lo hi N) lo hi hlohi
    (fun a ha=>(Finset.mem_filter.mp ha).2)
    (by
      intro a hla hah hz
      apply Finset.mem_filter.mpr
      exact ⟨lineEvents_mono (realRootsThrough_mono C e hN) v k
        (line_cut_event C pc e L hdeg v k H a hz),hla,hah⟩)
    (fun a _=>actualInfinityLine_square Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a) x
  rw [(AffineCut.sides_eq_of_ne _ _ lo hl).2,(AffineCut.sides_eq_of_ne _ _ hi hh).1] at HT
  simpa only [actualInfinityLineProductUnit,←innerHom_foldr,List.foldr_map,
    comparisonWordAction,actualLineWord,intervalEventList,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] using HT
end
end ElementaryPositivity.RationalFiber

end

end OAI
