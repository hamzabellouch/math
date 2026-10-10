import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.FiniteCovectorPerturbation
import OAI.Combinatorics.Chromatic.Walls.IncomingRayElement

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M E I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M]
  [AddCommGroup E] [Module ℝ E] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)
variable (e : M→+E) (he : Function.Injective e)
variable (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB : ∀x,B x x=0)
variable (hcomp : ∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L : Module.Dual ℝ E) (hdeg : ∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))

def planeRoots (r s : E) : AddSubmonoid M :=
  (Submodule.span ℝ {r,s}).toAddSubmonoid.comap e

lemma rootsThrough_spec {N : ℕ} {m : M} (H : m∈rootsThrough C N) :
    ∃n≤N,HasRootDegree C n m := by
  classical
  obtain ⟨n,hn,hm⟩:=Finset.mem_biUnion.mp H
  refine ⟨n,by have := Finset.mem_range.mp hn; omega,?_⟩
  simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hm

include he hB hcomp hdeg in

theorem planar_joint_factorization (r s : E) (hr : 0<L r) (hrs : B r s≠0)
    (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubring v Ω (planeRoots e r s)) (N : ℕ) :
    ∃l : List M,
      (∀p∈l,∃d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ p∈planeRoots e r s) ∧
      l.Pairwise (fun a b => 0<Ω a b) ∧
      (∀p∈l,∀n,n+1≤N → ∀m,
        coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m) ∧
      ∀n≤N,coeff n F.val=coeff n (completedListProduct v Ω C l
        (fun p => chartZero v Ω C (incomingCovector Ω p) F)).val := by
  classical
  let S:=(rootsThrough C N).filter (fun m => 0<L (e m) ∧ e m∈Submodule.span ℝ {r,s})
  have hS : ∀m∈S,0<L (e m) ∧ e m∈Submodule.span ℝ {r,s}:=fun m hm => (Finset.mem_filter.mp hm).2
  have hSmem : ∀m∈S,∃d,0<d ∧ d≤N ∧ HasRootDegree C d m ∧ m∈planeRoots e r s:=by
    intro m hm
    obtain ⟨d,hd,hrd⟩:=rootsThrough_spec C (Finset.mem_filter.mp hm).1
    have hp:= (hS m hm).1
    rw [hdeg d m hrd] at hp
    exact ⟨d,by exact_mod_cast hp,hd,hrd,(hS m hm).2⟩
  obtain ⟨l,hlS,hlpair,hlcover⟩:=finite_positive_ray_order e B hB L r s S hr hS
  have hl : ∀p∈l,∃d,0<d ∧ d≤N ∧ HasRootDegree C d p ∧ p∈planeRoots e r s:=
    fun p hp => hSmem p (hlS p hp)
  have hpair : l.Pairwise (fun a b => 0<Ω a b):=by
    apply hlpair.imp
    intro a b h
    rw [hcomp] at h
    exact_mod_cast h
  have hcover : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m → m∈planeRoots e r s →
      ∃p∈l,OnPositiveRay p m:=by
    intro n hn hnN m hm hmP
    have hmS : m∈S:=Finset.mem_filter.mpr ⟨mem_rootsThrough C N n hnN m hm,
      by rw [hdeg n m hm]; exact ⟨by exact_mod_cast hn,hmP⟩⟩
    obtain ⟨p,hp,hmp⟩:=hlcover m hmS
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    exact ⟨p,hp,positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p n d hn hd hm hdp hmP hpP hmp⟩
  have hRay : ∀p∈l,∀n,n+1≤N → ∀m,
      coeff (n+1) (chartZero v Ω C (incomingCovector Ω p) F).val m≠0 → OnPositiveRay p m:=by
    intro p hp n hn m hm
    obtain ⟨d,hd,hdN,hdp,hpP⟩:=hl p hp
    have hmr : HasRootDegree C (n+1) m:=by
      by_contra hh
      exact hm ((chartZero v Ω C (incomingCovector Ω p) F).property.2 (n+1) m hh)
    have hmP : m∈planeRoots e r s:=by
      by_contra hh
      exact hm ((chartThree_supported v Ω C (incomingCovector Ω p) (planeRoots e r s) F hF).2.1 (n+1) m hh)
    have hmp : B (e m) (e p)=0:=by
      rw [hcomp]
      exact (chart_three_support v Ω C (incomingCovector Ω p) F).2.1 n m hm
    exact positive_ray_of_pairing_zero e he B hB L r s C hdeg hrs m p (n+1) d
      (by omega) hd hmr hdp hmP hpP hmp
  have hΩ : ∀m,Ω m m=0:=by
    intro m
    have H:=hB (e m)
    rw [hcomp] at H
    exact_mod_cast H
  exact ⟨l,hl,hpair,hRay,joint_recovered_from_incoming v Ω C hΩ l F N (planeRoots e r s) hF hcover hpair hRay⟩
end
end ElementaryPositivity.QuantumTorus

end

end OAI
