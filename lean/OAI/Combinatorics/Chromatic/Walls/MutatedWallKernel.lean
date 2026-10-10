import Mathlib
import OAI.Combinatorics.Chromatic.Walls.GeometricMutationLines
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationOrientedCompatibility

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries WallUnits FiniteRayGeometry
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (u : Rˣ) (Ω : M →+ M →+ ℤ)
local instance : Ring (Torus u Ω) := Torus.instRing u Ω
local instance : AddCommMonoid (Torus u Ω) := (Torus.instRing u Ω).toAddCommMonoid
local instance : AddGroup (Torus u Ω) := (Torus.instRing u Ω).toAddGroup
lemma orientPowerSeries_submonoid (P : AddSubmonoid M) (b : Bool)
    (f : PowerSeries (Torus u Ω)) (hf : ∀n m,coeff n f m≠0 → m∈P) :
    ∀n m,coeff n (orientPowerSeries b f) m≠0 → m∈P := by
  cases b
  · exact inverse_support_addSubmonoid u Ω P f hf
  · exact hf
lemma one_kernel_support (h : M →+ ℝ) (n : ℕ) (m : M)
    (hm : coeff n (1 : PowerSeries (Torus u Ω)) m≠0) : h m=0 := by
  by_cases hn : n=0
  · subst n
    rw [coeff_zero_eq_constantCoeff_apply,constantCoeff_one] at hm
    have hm0 : m=0:=by
      by_contra hh
      exact hm (Finsupp.single_eq_of_ne hh)
    simp [hm0]
  · rw [coeff_one,ite_eq_right hn] at hm
    exact (hm rfl).elim

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M)
omit [DecidableEq I] in
lemma chartZero_kernel_support (h : M →+ ℝ) (T : CompletedPositive u Ω C) :
    ∀n m,coeff n (chartZero u Ω C h T).val m≠0 → h m=0 := by
  intro n m hm
  cases n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply,(chartZero u Ω C h T).property.1] at hm
    have hm0 : m=0:=by
      by_contra hh
      exact hm (Finsupp.single_eq_of_ne hh)
    simp [hm0]
  | succ n => exact (chart_three_support u Ω C h T).2.1 n m hm
end

noncomputable section
variable {M E I : Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E]
  [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ)) (pc : I)
variable (e : M →+ E) (he : Function.Injective e)
variable (S : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hS : ∀x,S x x=0)
variable (hcomp : ∀a b,S (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
local instance : Ring (Torus LaurentRay.vUnit Ω) := Torus.instRing LaurentRay.vUnit Ω
local instance : AddCommMonoid (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddCommMonoid
local instance : AddGroup (Torus LaurentRay.vUnit Ω) := (Torus.instRing LaurentRay.vUnit Ω).toAddGroup

lemma normalizedSimple_kernel_support (h : M →+ ℝ) (r : M) (hr : h r=0) :
    ∀n m,coeff n (normalizedSimple Ω r) m≠0 → h m=0 := by
  intro n m hm
  rw [normalizedSimple,coeff_raySeries] at hm
  have heq : m=n • r:=by
    by_contra hh
    exact hm (Finsupp.single_eq_of_ne hh)
  rw [heq,map_nsmul,hr,nsmul_zero]

include hS hcomp in
lemma mutationCompletion_kernel_support (pos : Bool) (h : Module.Dual ℝ E)
    (f : PowerSeries (Torus LaurentRay.vUnit Ω))
    (hf : ∀n m,coeff n f m≠0 → h (e m)=0) :
    ∀n m,coeff n (mutationCompletion Ω hΩ C coord pc pos LaurentRay.vUnit f) m≠0 →
      realSideCovector e S (simpleRoot C pc) pos h (e m)=0 := by
  intro n m hm
  obtain ⟨a,rfl⟩:=mutationLinearPiece_surjective Ω hΩ C pc pos m
  rw [mutationCompletion_coeff_read] at hm
  split_ifs at hm with hd
  · obtain ⟨j,hj,hja⟩:=Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [realSideCovector_mutated_incidence Ω C pc pos e S hS hcomp]
    exact hf j a hja
  · exact (hm rfl).elim

variable (v k : Module.Dual ℝ E)
variable (H : ∀N,GenericOffset (realRootsThrough e C N) 0 v k)
include hS hcomp in
lemma mutatedLineFactor_kernel (a : ℝ) :
    ∀n m,coeff n (mutatedLineFactor Ω hΩ C coord pc e he L hdeg v k H a) m≠0 →
      realMutationCovector e S (simpleRoot C pc) (k+a • v) (e m)=0 := by
  classical
  unfold mutatedLineFactor
  split
  · next ha=>
    split
    · next hp=>
      have hcut : realMutationCovector e S (simpleRoot C pc) (k+a • v)=k+a • v:=by
        unfold realMutationCovector
        rw [ite_eq_left (le_of_eq hp.symm)]
      rw [hcut]
      apply orientPowerSeries_submonoid LaurentRay.vUnit Ω
        (((k+a • v).toAddMonoidHom.comp e).ker.toAddSubmonoid)
      apply normalizedSimple_kernel_support
      rw [mutatedRoot_p,map_neg]
      change -((k+a • v) (e (simpleRoot C pc)))=0
      rw [hp,neg_zero]
    · next hp=>
      let pos:=decide (0<(k+a • v) (e (simpleRoot C pc)))
      have hs : if pos then 0≤(k+a • v) (e (simpleRoot C pc)) else
          (k+a • v) (e (simpleRoot C pc))≤0:=by
        dsimp [pos]
        split_ifs with hh
        · exact le_of_lt (of_decide_eq_true hh)
        · exact le_of_not_gt (by simpa only [decide_eq_true_eq] using hh)
      rw [realMutationCovector_eq_side e S (simpleRoot C pc) pos _ hs]
      apply mutationCompletion_kernel_support Ω hΩ C coord pc e S hS hcomp pos
      apply orientPowerSeries_submonoid LaurentRay.vUnit Ω
        (((k+a • v).toAddMonoidHom.comp e).ker.toAddSubmonoid)
      exact chartZero_kernel_support LaurentRay.vUnit Ω C _ _
  · exact one_kernel_support LaurentRay.vUnit Ω
      ((realMutationCovector e S (simpleRoot C pc) (k+a • v)).toAddMonoidHom.comp e)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
