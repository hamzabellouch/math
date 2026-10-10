import Mathlib
import OAI.Combinatorics.Chromatic.Walls.GenericLineJoining

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

def mutatedPathProduct {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) (N : ℕ) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  match p with
  | .nil _=>1
  | .append s p=>mutatedLineProduct Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi N*
      mutatedPathProduct p N

def mutatedPathCompletion {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    PowerSeries (Torus LaurentRay.vUnit Ω) :=
  match p with
  | .nil _=>1
  | .append s p=>mutatedLineCompletion Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic s.lo s.hi*
      mutatedPathCompletion p

lemma mutatedPathCompletion_coeff {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b)
    (D N : ℕ) (hN : 1≤N) (hDN : (mutationSize Ω C pc+1)*D≤N) :
    ∀d≤D,coeff d (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)=
      coeff d (mutatedPathProduct Ω hΩ C coord pc e he L hdeg p N) := by
  induction p with
  | nil=>exact fun _ _=>rfl
  | append s p ih=>
    intro d hd
    apply FormalLog.mul_coeff_congr
    · intro j hj
      exact mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg s.direction s.offset s.generic
        s.lo s.hi j N hN ((Nat.mul_le_mul_left _ (hj.trans hd)).trans hDN)
    · intro j hj
      exact ih j (hj.trans hd)

lemma mutatedPathCompletion_trans {a b c : Module.Dual ℝ E}
    (p : GenericLinePath C e a b) (q : GenericLinePath C e b c) :
    mutatedPathCompletion Ω hΩ C coord pc e he L hdeg (p.trans C e q)=
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg q*
      mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p := by
  induction q with
  | nil=>exact (one_mul _).symm
  | append s q ih=>
    simp only [GenericLinePath.trans,mutatedPathCompletion,ih,mul_assoc]

lemma mutatedPathCompletion_constant {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    constantCoeff (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p)=1 := by
  induction p with
  | nil=>exact constantCoeff_one
  | append s p ih=>
    simp only [mutatedPathCompletion,map_mul,mutatedLineCompletion_constant,ih,one_mul]

variable (hcoord : ∀d,coord (C d)=d)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
include hcoord hS hcomp in
lemma mutatedPathCompletion_graded {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p) := by
  induction p with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | append s p ih=>
    exact (mutatedLineCompletion_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg
      s.direction s.offset s.generic s.lo s.hi).mul LaurentRay.vUnit Ω _ ih

def mutatedPathCompletedPositive {a b : Module.Dual ℝ E} (p : GenericLinePath C e a b) :
    CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedPathCompletion Ω hΩ C coord pc e he L hdeg p,
    mutatedPathCompletion_constant Ω hΩ C coord pc e he L hdeg p,
    mutatedPathCompletion_graded Ω hΩ C coord pc e he L hdeg hcoord S hS hcomp p⟩
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry RationalFiber
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
lemma mutationCompletion_list_prod (pos : Bool) (l : List (PowerSeries (Torus LaurentRay.vUnit Ω)))
    (h : ∀f∈l,RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
      (mutationSize Ω C pc+1) f) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit l.prod=
      (l.map (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit)).prod := by
  have H : RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
      (mutationSize Ω C pc+1) l.prod ∧
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit l.prod=
        (l.map (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit)).prod := by
    induction l with
    | nil=>exact ⟨RegradeBound.one _ _ _ _,mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit⟩
    | cons f l ih=>
      obtain ⟨hl,he⟩:=ih (fun x hx=>h x (List.mem_cons_of_mem f hx))
      have hf:=h f (by simp)
      refine ⟨hf.mul _ _ _ _ hl,?_⟩
      rw [List.prod_cons,mutationCompletion_mul Ω hΩ C coord pc pos LaurentRay.vUnit hf hl,he]
      rfl
  exact H.2

variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)

def noncutOldLineFactor (a : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) := by
  classical
  exact if ha : ∃N,a∈lineEvents (realRootsThrough e C N) v k then
    let data:=lineRayData C e he L hdeg v k H a ha
    orientPowerSeries (decide (v (e data.root)<0))
      (chartZero LaurentRay.vUnit Ω C ((k+a • v).toAddMonoidHom.comp e) (simpleTotalTransport Ω C)).val
  else 1

lemma cutSide_decision (pos : Bool) (h : M →+ ℝ) (p : M) (hs : cutSide pos h p) :
    h p≠0 ∧ decide (0<h p)=pos := by
  cases pos
  · change h p<0 at hs
    exact ⟨ne_of_lt hs,decide_eq_false (not_lt_of_ge (le_of_lt hs))⟩
  · change 0<h p at hs
    exact ⟨ne_of_gt hs,decide_eq_true hs⟩

lemma mutatedLineFactor_nocut (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a=
      mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit
        (noncutOldLineFactor Ω C e he L hdeg v k H a) := by
  classical
  obtain ⟨hp,hpos⟩:=cutSide_decision pos _ _ hs
  change (k+a • v) (e (simpleRoot C pc))≠0 at hp
  change decide (0<(k+a • v) (e (simpleRoot C pc)))=pos at hpos
  unfold mutatedLineFactor noncutOldLineFactor
  split
  · next ha=>simp only; rw [hpos]
  · next ha=>exact (mutationCompletion_one Ω hΩ C coord pc pos LaurentRay.vUnit).symm

include hΩ hcoord hS hcomp in
lemma noncutOldLineFactor_bound (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos) (mutationSize Ω C pc+1)
      (noncutOldLineFactor Ω C e he L hdeg v k H a) := by
  classical
  unfold noncutOldLineFactor
  split
  · next ha=>
    let data:=lineRayData C e he L hdeg v k H a ha
    have hf:=simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
      data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic pos hs
    have hb:=mutationCompletion_bound Ω hΩ C coord hcoord pc pos LaurentRay.vUnit _ hf
    change RegradeBound _ _ _ _ (orientPowerSeries (decide (v (e data.root)<0)) _)
    cases hb' : decide (v (e data.root)<0)
    · exact hb.invOfUnit LaurentRay.vUnit Ω _ _
    · exact hb
  · exact RegradeBound.one _ _ _ _

include hcoord hS hcomp in
lemma noncutOldLineFactor_comparison (pos : Bool) (a : ℝ)
    (hs : cutSide pos ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc)) :
    noncutOldLineFactor Ω C e he L hdeg v k H a=
      (comparisonOld LaurentRay.vUnit Ω hΩ (nonpDegree coord pc) (pureDegree coord pc)
        (simpleRoot C pc) (pureDegree_simple_self C coord hcoord pc)
        (nonpDegree_simple_self C coord hcoord pc) (mutationSize Ω C pc+1)
        (actualLineLetter Ω C coord hcoord pc e he S hS hcomp L hdeg v k H a)).val.val := by
  classical
  have hp:=(cutSide_decision pos _ _ hs).1
  change (k+a • v) (e (simpleRoot C pc))≠0 at hp
  unfold noncutOldLineFactor actualLineLetter
  split
  · next ha=>
    simp only
    let data:=lineRayData C e he L hdeg v k H a ha
    cases hh : decide (v (e data.root)<0) <;>
      simp only [orientPowerSeries,orientedBounded,Bool.false_eq_true,ite_false,ite_true,
        comparisonOld,completedBiUnit_val]
    all_goals rfl
  · next ha=>simp only [comparisonOld]; rfl
end
end ElementaryPositivity.QuantumTorus

end

end OAI
