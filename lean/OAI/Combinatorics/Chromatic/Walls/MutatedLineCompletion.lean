import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteRefinementImportAll

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries
noncomputable section
variable {A J : Type*} [Ring A]
lemma filter_product_coeff_congr (l : List J) (p : J → Bool) (f : J → PowerSeries A) (D : ℕ)
    (h : ∀a∈l,p a=false → ∀n≤D,coeff n (f a)=coeff n 1) :
    ∀n≤D,coeff n ((l.filter p).map f).prod=coeff n (l.map f).prod := by
  induction l with
  | nil=>exact fun _ _=>rfl
  | cons a l ih=>
    have ih':=ih (fun x hx hp=>h x (List.mem_cons_of_mem a hx) hp)
    by_cases hp : p a=true
    · simp only [List.filter_cons,hp,↓reduceIte,List.map_cons,List.prod_cons]
      intro n hn
      exact FormalLog.mul_coeff_congr _ _ _ _ n (fun _ _=>rfl)
        (fun j hj=>ih' j (hj.trans hn))
    · have hp' : p a=false:=Bool.eq_false_iff.mpr hp
      simp only [List.filter_cons,hp',Bool.false_eq_true,ite_false,List.map_cons,List.prod_cons]
      intro n hn
      rw [←one_mul (((l.filter p).map f).prod)]
      exact FormalLog.mul_coeff_congr _ _ _ _ n
        (fun j hj=>(h a (by simp) hp' j (hj.trans hn)).symm)
        (fun j hj=>ih' j (hj.trans hn))
end
end ElementaryPositivity.PowerSeriesAdjoint

namespace ElementaryPositivity.QuantumTorus
open PowerSeries FiniteRayGeometry WallUnits
noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma mutatedLineProduct_stabilizes (lo hi : ℝ) (D A N : ℕ) (hA : 1≤A)
    (hDA : (mutationSize Ω C pc+1)*D≤A) (hAN : A≤N) :
    ∀n≤D,coeff n (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi A)=
      coeff n (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  classical
  unfold mutatedLineProduct
  rw [←intervalEventList_filter C e v k lo hi hAN]
  apply PowerSeriesAdjoint.filter_product_coeff_congr
  intro a ha hp
  exact mutatedLineFactor_high Ω hΩ C coord pc e he L hdeg v k H D A hA hDA a
    (event_not_retained C e v k lo hi a ha (of_decide_eq_false hp))

def mutatedLineCompletion (lo hi : ℝ) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  PowerSeries.mk (fun d=>coeff d (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi
    (max 1 ((mutationSize Ω C pc+1)*d))))

lemma mutatedLineCompletion_coeff (lo hi : ℝ) (d N : ℕ) (hN : 1≤N)
    (hdN : (mutationSize Ω C pc+1)*d≤N) :
    coeff d (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)=
      coeff d (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  simp only [mutatedLineCompletion,PowerSeries.coeff_mk]
  exact mutatedLineProduct_stabilizes Ω hΩ C coord pc e he L hdeg v k H lo hi d
    (max 1 ((mutationSize Ω C pc+1)*d)) N (le_max_left _ _) (le_max_right _ _)
    (max_le hN hdN) d le_rfl
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {A : Type*} [Ring A]
lemma orientPowerSeries_constant (b : Bool) (f : PowerSeries A) (hf : constantCoeff f=1) :
    constantCoeff (orientPowerSeries b f)=1 := by
  cases b
  · simp only [orientPowerSeries,Bool.false_eq_true,ite_false,constantCoeff_invOfUnit,
      inv_one,Units.val_one]
  · exact hf
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup
omit [DecidableEq I] in
lemma orientPowerSeries_graded (b : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : SeriesGraded LaurentRay.vUnit Ω C f) :
    SeriesGraded LaurentRay.vUnit Ω C (orientPowerSeries b f) := by
  cases b
  · exact hf.inverse LaurentRay.vUnit Ω C
  · exact hf

lemma mutationCompletion_inverse (pos : Bool) (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : RegradeBound LaurentRay.vUnit Ω (mutationNewOrder Ω C coord pc pos)
      (mutationSize Ω C pc+1) f) (hc : constantCoeff f=1) :
    mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (invOfUnit f 1)=
      invOfUnit (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) 1 := by
  let g:=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f
  let gi:=mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (invOfUnit f 1)
  have hleft : gi*g=1:=mutationCompletion_inverse_mul Ω hΩ C coord pc pos LaurentRay.vUnit hf hc
  have hright : g*invOfUnit g 1=1:=PowerSeries.mul_invOfUnit g 1
    (mutationCompletion_constant Ω hΩ C coord pc pos LaurentRay.vUnit f hc)
  change gi=invOfUnit g 1
  calc gi=gi*1:=(mul_one gi).symm
       _=gi*(g*invOfUnit g 1):=by rw [hright]
       _=(gi*g)*invOfUnit g 1:=(mul_assoc _ _ _).symm
       _=invOfUnit g 1:=by rw [hleft,one_mul]

include hcoord in
lemma mutationCompletion_orient_graded (pos b : Bool) (f : CompletedPositive LaurentRay.vUnit Ω C)
    (hf : ∀n m,coeff n f.val m≠0 → m∈fiberCone coord pc (mutationPairing Ω C pc) (sideSign pos)) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit (orientPowerSeries b f.val)) := by
  have hg : SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f.val):=
    mutationCompletion_graded Ω hΩ C coord hcoord pc pos LaurentRay.vUnit f hf
  cases b
  · simp only [orientPowerSeries,Bool.false_eq_true,ite_false]
    rw [mutationCompletion_inverse Ω hΩ C coord pc pos f.val
      (mutationCompletion_bound Ω hΩ C coord hcoord pc pos LaurentRay.vUnit f hf) f.property.1]
    exact hg.inverse LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
  · exact hg

variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
lemma mutatedLineFactor_constant (a : ℝ) :
    constantCoeff (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a)=1 := by
  classical
  unfold mutatedLineFactor
  split
  · split
    · exact orientPowerSeries_constant _ _ (normalizedSimple_constant Ω _)
    · exact mutationCompletion_constant Ω hΩ C coord pc _ LaurentRay.vUnit _
        (orientPowerSeries_constant _ _ (chartZero _ _ _ _ _).property.1)
  · exact constantCoeff_one

include hcoord hS hcomp in
lemma mutatedLineFactor_graded (a : ℝ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a) := by
  classical
  unfold mutatedLineFactor
  split
  · next ha=>
    split
    · apply orientPowerSeries_graded
      rw [←simpleDatum_value Ω (mutatedRoots Ω C pc) pc]
      exact WallUnitDatum.graded Ω _ (fun _=>True) _ (simpleDatum_allowed _ pc)
    · next hp=>
      let data:=lineRayData C e he L hdeg v k H a ha
      apply mutationCompletion_orient_graded Ω hΩ C coord hcoord pc
      exact simple_fiber_bound Ω C coord hcoord pc e he S hS hcomp L hdeg
        data.root data.degree data.degree_pos data.root_degree (k+a • v) data.generic _
        (cutSide_decide ((k+a • v).toAddMonoidHom.comp e) (simpleRoot C pc) hp)
  · exact SeriesGraded.one LaurentRay.vUnit Ω _

lemma mutatedLineProduct_constant (lo hi : ℝ) (N : ℕ) :
    constantCoeff (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N)=1 := by
  unfold mutatedLineProduct
  induction intervalEventList C e v k lo hi N with
  | nil=>simp
  | cons a l ih=>
    simp only [List.map_cons,List.prod_cons,map_mul,mutatedLineFactor_constant,one_mul,ih]

include hcoord hS hcomp in
lemma mutatedLineProduct_graded (lo hi : ℝ) (N : ℕ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineProduct Ω hΩ C coord pc e he L hdeg v k H lo hi N) := by
  unfold mutatedLineProduct
  induction intervalEventList C e v k lo hi N with
  | nil=>exact SeriesGraded.one LaurentRay.vUnit Ω _
  | cons a l ih=>
    exact (mutatedLineFactor_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H a).mul
      LaurentRay.vUnit Ω _ ih

lemma mutatedLineCompletion_constant (lo hi : ℝ) :
    constantCoeff (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi)=1 := by
  rw [←coeff_zero_eq_constantCoeff_apply,mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi 0 1 le_rfl (by omega),
    coeff_zero_eq_constantCoeff_apply,mutatedLineProduct_constant]

include hcoord hS hcomp in
lemma mutatedLineCompletion_graded (lo hi : ℝ) :
    SeriesGraded LaurentRay.vUnit Ω (mutatedRoots Ω C pc)
      (mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi) := by
  intro d
  rw [mutatedLineCompletion_coeff Ω hΩ C coord pc e he L hdeg v k H lo hi d
    (max 1 ((mutationSize Ω C pc+1)*d)) (le_max_left _ _) (le_max_right _ _)]
  exact mutatedLineProduct_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi _ d

def mutatedLineCompletedPositive (lo hi : ℝ) : CompletedPositive LaurentRay.vUnit Ω (mutatedRoots Ω C pc) :=
  ⟨mutatedLineCompletion Ω hΩ C coord pc e he L hdeg v k H lo hi,
    mutatedLineCompletion_constant Ω hΩ C coord pc e he L hdeg v k H lo hi,
    mutatedLineCompletion_graded Ω hΩ C coord hcoord pc e he S hS hcomp L hdeg v k H lo hi⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
