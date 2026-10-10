import Mathlib
import OAI.Combinatorics.Chromatic.Walls.QuantumTorusChartCompletion

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (p : I)
def simpleRoot : M := C (Pi.single p 1)
def nonpDegree : M →+ ℤ where
  toFun m:=∑i∈Finset.univ.erase p,coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [Finset.sum_add_distrib]
def fiberUpper (α : I → ℤ) (σ : ℤ) : M →+ ℤ where
  toFun m:=∑i∈Finset.univ.erase p,max 0 (-σ*α i)*coord m i
  map_zero':=by simp
  map_add':=by intro a b; simp [mul_add,Finset.sum_add_distrib]
def fiberCone (α : I → ℤ) (σ : ℤ) : AddSubmonoid M where
  carrier:={m | 0≤coord m p ∧ coord m p≤fiberUpper coord p α σ m}
  zero_mem':=by simp
  add_mem':=by
    intro a b ha hb
    change 0≤coord (a+b) p ∧ coord (a+b) p≤fiberUpper coord p α σ (a+b)
    simp only [map_add,Pi.add_apply]
    exact ⟨add_nonneg ha.1 hb.1,add_le_add ha.2 hb.2⟩
include hcoord in
omit [DecidableEq I] in
lemma root_coordinates {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    ∃d : I → ℕ,(∑i,d i)=n ∧ (∀i,coord m i=(d i:ℤ)) ∧ C (fun i=>(d i:ℤ))=m := by
  obtain ⟨d,hd,hm⟩:=hm
  refine ⟨d,hd,?_,hm⟩
  rw [←hm,hcoord]
  exact fun _=>rfl
include hcoord in
lemma nonpDegree_root_nonneg {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    0≤nonpDegree coord p m := by
  obtain ⟨d,hd,hc,hm⟩:=root_coordinates C coord hcoord hm
  change 0≤∑i∈Finset.univ.erase p,coord m i
  apply Finset.sum_nonneg
  intro i hi
  rw [hc]
  positivity
include hcoord in
lemma nonpDegree_root_eq {n : ℕ} {m : M} (hm : HasRootDegree C n m) :
    nonpDegree coord p m+coord m p=(n:ℤ) := by
  obtain ⟨d,hd,hc,hm⟩:=root_coordinates C coord hcoord hm
  change (∑i∈Finset.univ.erase p,coord m i)+coord m p=(n:ℤ)
  rw [Finset.sum_erase_add _ _ (Finset.mem_univ p)]
  simp only [hc,←Nat.cast_sum,hd]
include hcoord in
lemma nonp_zero_root {n : ℕ} {m : M} (hm : HasRootDegree C n m)
    (hz : nonpDegree coord p m=0) : m=n • simpleRoot C p := by
  obtain ⟨d,hd,hc,he⟩:=root_coordinates C coord hcoord hm
  have hs : ∑i∈Finset.univ.erase p,(d i:ℤ)=0:=by simpa only [nonpDegree,AddMonoidHom.coe_mk,ZeroHom.coe_mk,hc] using hz
  have hz' : ∀i,i≠p → d i=0:=by
    intro i hi
    have HH:=Finset.sum_eq_zero_iff_of_nonneg (fun i (hi : i∈Finset.univ.erase p)=>Int.natCast_nonneg (d i)) |>.mp hs i (Finset.mem_erase.mpr ⟨hi,Finset.mem_univ i⟩)
    exact_mod_cast HH
  have hdp : d p=n:=by
    rw [←hd,Finset.sum_eq_single p]
    · intro i hi hp; exact hz' i hp
    · simp
  have hds : (fun i=>(d i:ℤ))=n • (Pi.single p 1 : I → ℤ):=by
    ext i
    by_cases hi : i=p
    · subst i; simp [hdp]
    · simp [hz' i hi,hi]
  rw [←he,hds,map_nsmul]
  rfl
include hcoord in
lemma nonp_positive_off_cut {n : ℕ} (hn : 0<n) {m : M} (hm : HasRootDegree C n m)
    (h : M →+ ℝ) (hp : h (simpleRoot C p)≠0) (hm0 : h m=0) :
    0<nonpDegree coord p m := by
  have hnon:=nonpDegree_root_nonneg C coord hcoord p hm
  by_contra hh
  have hz : nonpDegree coord p m=0:=by omega
  rw [nonp_zero_root C coord hcoord p hm hz,map_nsmul] at hm0
  have hnR : (n:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hn)
  exact hp ((mul_eq_zero.mp (show (n:ℝ)*h (simpleRoot C p)=0 by simpa only [nsmul_eq_mul] using hm0)).resolve_left hnR)
end
end ElementaryPositivity.QuantumTorus

end

end OAI
