import Mathlib
import OAI.Combinatorics.Chromatic.Walls.HNTorusFactor
import OAI.Combinatorics.Chromatic.GradedAlgebra.InputOrderedProduct

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open RawShuffle QuantumTorus PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

lemma crossInteraction_axis (i : I) (d : I → ℕ) (hd : Supported {i} d) : crossInteraction a d=0 := by
  rw [crossInteraction_offdiagonal]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hjk : j=k
  · simp [hjk]
  · rw [ite_eq_right hjk]
    by_cases hji : j=i
    · subst j
      rw [hd k (by simp [Ne.symm hjk]),Nat.cast_zero,mul_zero]
    · rw [hd j (by simp [hji]),Nat.cast_zero,mul_zero,zero_mul]

lemma partialCoefficient_singleton (i : I) :
    partialCoefficient a u v {i}=supportedCoefficient {i} (fun d=>u i (d i)) := by
  funext d
  rw [partialCoefficient,supportedCoefficient,supportedCoefficient]
  by_cases hd : Supported {i} d
  · rw [ite_eq_left hd,ite_eq_left hd]
    simp only [Finset.prod_singleton,crossInteraction_axis a i d hd,zpow_zero,Units.val_one,mul_one]
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]

lemma push_partial_axis (i : I) (f : PowerSeries R) :
    push w v Ω P (partialCoefficient a (fun _ n=>coeff n f) v {i})=
      weightedRay v Ω (w i) (P (Pi.single i 1)) f := by
  rw [partialCoefficient_singleton,push_axis]

lemma push_partial_axis_family (i : I) (f : I → PowerSeries R) :
    push w v Ω P (partialCoefficient a (fun j n=>coeff n (f j)) v {i})=
      weightedRay v Ω (w i) (P (Pi.single i 1)) (f i) := by
  rw [partialCoefficient_singleton,push_axis]

end
end ElementaryPositivity.WeightedTorusSeries

namespace ElementaryPositivity.RawShuffle
open QuantumTorus WeightedTorusSeries PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (w : I → ℕ) [Fact (∀i,0<w i)]

def literalAxisScalar (i : I) : PowerSeries (LaurentSeries ℚ) :=
  PowerSeries.map LaurentRay.atInfinity (UnitSelections.indexedUnit (elementaryDiagonal ε i) (κ i))

def literalAxis (i : I) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω (w i) (P (Pi.single i 1)) (literalAxisScalar κ ε i)

omit [DecidableEq I] in
lemma partial_univ_literal :
    partialCoefficient a (fun i n=>coeff n (literalAxisScalar κ ε i)) LaurentRay.vUnit Finset.univ=
      literalInputCoefficient a κ ε := by
  funext d
  have HS : Supported Finset.univ d := by intro i hi; exact (hi (Finset.mem_univ i)).elim
  rw [partialCoefficient,supportedCoefficient,ite_eq_left HS]
  dsimp only [literalAxisScalar]
  simp only [coeff_map,LaurentRay.vUnit_zpow]
  rfl

theorem literalInput_ordered (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
    (l : List I) (hl : l.Nodup) (hall : l.toFinset=Finset.univ)
    (ho : l.Pairwise fun i j=>a i j=0) :
    push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)=
      (l.map (literalAxis κ ε Ω P w)).prod := by
  have H:=push_partial_list a (fun i n=>coeff n (literalAxisScalar κ ε i))
    LaurentRay.vUnit Ω P hΩ w l hl ho
  rw [hall,partial_univ_literal a κ ε] at H
  rw [H]
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact push_partial_axis_family a LaurentRay.vUnit Ω P w i (literalAxisScalar κ ε)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : I → M) (ε : I → Bool)

def geometricQuiver (i j : I) : ℕ :=
  if i=j then elementaryDiagonal ε i else (Ω (p j) (p i)).toNat

def rootSum : (I→ℕ) →+ M where
  toFun d:=∑i,d i • p i
  map_zero':=by simp
  map_add':=by intro d e; simp only [Pi.add_apply,add_nsmul,Finset.sum_add_distrib]

lemma rootSum_single (i : I) (n : ℕ) : rootSum p (Pi.single i n)=n • p i := by
  classical
  simp [rootSum,Pi.single_apply,ite_smul,Finset.sum_ite_eq']

omit [Fintype I] in
lemma geometricQuiver_diag (i : I) : geometricQuiver Ω p ε i i=elementaryDiagonal ε i := by
  simp [geometricQuiver]

variable (hΩ : ∀m,Ω m m=0)
omit [Fintype I] in
include hΩ in
lemma geometricQuiver_skew (i j : I) :
    (geometricQuiver Ω p ε j i:ℤ)-geometricQuiver Ω p ε i j=Ω (p i) (p j) := by
  by_cases h : i=j
  · subst j; rw [sub_self,hΩ]
  · rw [geometricQuiver,ite_eq_right (Ne.symm h),geometricQuiver,ite_eq_right h,
      alternating_skew Ω hΩ (p j) (p i)]
    omega

include hΩ in
lemma geometricQuiver_euler (d e : I→ℕ) :
    Ω (rootSum p d) (rootSum p e)=
      eulerForm (geometricQuiver Ω p ε) d e-eulerForm (geometricQuiver Ω p ε) e d := by
  rw [euler_skew_sum]
  simp only [rootSum,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sum,map_nsmul,
    AddMonoidHom.finsetSum_apply,AddMonoidHom.nsmul_apply,nsmul_eq_mul,
    geometricQuiver_skew Ω p ε hΩ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_forward (i j : I) (hij : i≠j) (hp : 0≤Ω (p i) (p j)) :
    geometricQuiver Ω p ε i j=0 := by
  rw [geometricQuiver,ite_eq_right hij,alternating_skew Ω hΩ (p j) (p i)]
  exact Int.toNat_eq_zero.mpr (by omega)

omit [Fintype I] in
include hΩ in
lemma geometricQuiver_pairwise (l : List I) (hn : l.Nodup)
    (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j))) :
    l.Pairwise (fun i j=>geometricQuiver Ω p ε i j=0) := by
  apply (hn.and hl).imp
  intro i j h
  exact geometricQuiver_forward Ω p ε hΩ i j h.1 h.2

include hΩ in
lemma geometricQuiver_symmetric (c η : I→ℝ) (hc : ∀i,0<c i) (t : ℝ)
    (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j)) :
    ∀θ,SlopeEulerSymmetric (geometricQuiver Ω p ε) c η θ := by
  apply slopeEulerSymmetric_of_plane _ c η hc t
  intro i j
  have H:=congrArg (fun z:ℤ=>(z:ℝ)) (geometricQuiver_skew Ω p ε hΩ i j)
  push_cast at H
  exact H.trans (hp i j)

end
end ElementaryPositivity.RawShuffle

end

end OAI
