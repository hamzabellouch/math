import Mathlib

namespace OAI

section
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R:Type*} [CommRing R]

def exponentOrbit (μ:σ →₀ ℕ) : Finset (σ →₀ ℕ) :=
  Finset.univ.image (fun e:Equiv.Perm σ=>μ.mapDomain e)

def polynomial (μ:σ →₀ ℕ) : MvPolynomial σ R :=
  ∑d∈exponentOrbit μ,MvPolynomial.monomial d 1

lemma exponentOrbit_self (μ:σ →₀ ℕ) : μ∈exponentOrbit μ := by
  refine Finset.mem_image.mpr ⟨Equiv.refl σ,Finset.mem_univ _,?_⟩
  exact Finsupp.mapDomain_id

lemma exponentOrbit_map (μ:σ →₀ ℕ) (e:Equiv.Perm σ) (d:σ →₀ ℕ)
    (hd:d∈exponentOrbit μ) : d.mapDomain e∈exponentOrbit μ := by
  obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp hd
  refine Finset.mem_image.mpr ⟨f.trans e,Finset.mem_univ _,?_⟩
  exact Finsupp.mapDomain_comp (v:=μ) (f:=f) (g:=e)

lemma exponentOrbit_map_iff (μ:σ →₀ ℕ) (e:Equiv.Perm σ) (d:σ →₀ ℕ) :
    d.mapDomain e∈exponentOrbit μ ↔ d∈exponentOrbit μ := by
  constructor
  · intro h
    have H:=exponentOrbit_map μ e.symm _ h
    simpa only [←Finsupp.mapDomain_comp,Equiv.symm_comp_self,Finsupp.mapDomain_id] using H
  · exact exponentOrbit_map μ e d

lemma coeff_polynomial (μ d:σ →₀ ℕ) : (polynomial μ: MvPolynomial σ R).coeff d=
    if d∈exponentOrbit μ then 1 else 0 := by
  simp [polynomial,MvPolynomial.coeff_monomial,eq_comm]

lemma polynomial_symmetric (μ:σ →₀ ℕ) : (polynomial μ:MvPolynomial σ R).IsSymmetric := by
  intro e
  apply MvPolynomial.ext
  intro d
  let d':=d.mapDomain e.symm
  have he:d'.mapDomain e=d:=by
    simp only [d',←Finsupp.mapDomain_comp,Equiv.self_comp_symm,Finsupp.mapDomain_id]
  rw [←he,MvPolynomial.coeff_rename_mapDomain e e.injective,coeff_polynomial,coeff_polynomial]
  simp only [exponentOrbit_map_iff]

lemma polynomial_homogeneous (μ:σ →₀ ℕ) :
    (polynomial μ:MvPolynomial σ R).IsHomogeneous μ.degree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hd
  exact MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_mapDomain e μ)

lemma dominant_orbit_unique {n:ℕ} (μ ν:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc)
    (h:ν∈exponentOrbit μ) : ν=μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp h
  have hfun:(fun i=>(μ.mapDomain e) i)=(fun i=>μ (e.symm i)):=by
    funext i
    let a:=e.symm i
    have H:=Finsupp.mapDomain_apply_of_injective e.injective μ a
    simpa only [a,Equiv.apply_symm_apply] using H
  have hp:(List.ofFn (fun i=>(μ.mapDomain e) i)).Perm (List.ofFn (fun i=>μ i)):=by
    rw [hfun]
    exact Equiv.Perm.ofFn_comp_perm (e.symm : Equiv.Perm _) _
  have H:=List.Perm.eq_of_pairwise' (r:=fun a b:ℕ=>b ≤ a)
    (List.pairwise_ofFn.mpr (fun i j hij=>(Fin.antitone_iff_succ_le.mpr hν) (le_of_lt hij)))
    (List.pairwise_ofFn.mpr (fun i j hij=>(Fin.antitone_iff_succ_le.mpr hμ) (le_of_lt hij))) hp
  exact DFunLike.coe_injective (List.ofFn_injective H)

lemma dominant_coeff {n:ℕ} (μ ν:Fin (n+1) →₀ ℕ)
    (hμ:∀i:Fin n,μ i.succ ≤ μ i.castSucc) (hν:∀i:Fin n,ν i.succ ≤ ν i.castSucc) :
    (polynomial μ:MvPolynomial (Fin (n+1)) R).coeff ν=if ν=μ then 1 else 0 := by
  rw [coeff_polynomial]
  congr 1
  exact propext ⟨dominant_orbit_unique μ ν hμ hν,fun h=>h ▸ exponentOrbit_self μ⟩
end
end ElementaryPositivity.OrbitMonomial

end
section
namespace ElementaryPositivity.OrbitMonomial
open scoped BigOperators
open Classical
noncomputable section
variable {σ:Type*} [Fintype σ] [DecidableEq σ] {R:Type*} [CommRing R]

lemma exponentOrbit_symm {μ d:σ →₀ ℕ} (h:d∈exponentOrbit μ) : μ∈exponentOrbit d := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp h
  have H:=exponentOrbit_map (μ.mapDomain e) e.symm _ (exponentOrbit_self _)
  simpa only [←Finsupp.mapDomain_comp,Equiv.symm_comp_self,Finsupp.mapDomain_id] using H
lemma exponentOrbit_trans {μ d k:σ →₀ ℕ} (hd:d∈exponentOrbit μ) (hk:k∈exponentOrbit d) :
    k∈exponentOrbit μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hk
  exact exponentOrbit_map μ e d hd
lemma symmetric_coeff_orbit (p:MvPolynomial σ R) (hp:p.IsSymmetric) (μ d:σ →₀ ℕ)
    (hd:d∈exponentOrbit μ) : p.coeff d=p.coeff μ := by
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hd
  have H := MvPolynomial.coeff_rename_mapDomain e e.injective p μ
  simpa only [hp e] using H

lemma dominant_representative {n:ℕ} (d:Fin (n+1) →₀ ℕ) :
    ∃μ:Fin (n+1) →₀ ℕ,(∀i:Fin n,μ i.succ ≤ μ i.castSucc) ∧ d∈exponentOrbit μ := by
  let e:Equiv.Perm (Fin (n+1)):=Tuple.sort (α:=OrderDual ℕ) (fun i=>d i)
  let μ:=d.mapDomain e.symm
  have H:∀i,μ i=d (e i):=by
    intro i
    simpa only [μ,Equiv.symm_apply_apply] using (Finsupp.mapDomain_apply_of_injective e.symm.injective d (e i))
  refine ⟨μ,?_,exponentOrbit_symm (exponentOrbit_map d e.symm d (exponentOrbit_self d))⟩
  intro i
  rw [H,H]
  have hm := Tuple.monotone_sort (α:=OrderDual ℕ) (fun j : Fin (n+1) => d j)
  exact hm (Fin.castSucc_le_succ i)

lemma symmetric_orbit_decomposition {n:ℕ} (p:MvPolynomial (Fin (n+1)) R) (hp:p.IsSymmetric) :
    p=∑μ∈p.support.filter (fun μ=>∀i:Fin n,μ i.succ ≤ μ i.castSucc),
      MvPolynomial.C (p.coeff μ)*polynomial μ := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨μ,hμ,hd⟩:=dominant_representative d
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul,coeff_polynomial]
  symm
  rw [Finset.sum_eq_single μ]
  · rw [ite_eq_left hd,mul_one]
    exact (symmetric_coeff_orbit p hp μ d hd).symm
  · intro ν hν hne
    obtain ⟨_,hν⟩:=Finset.mem_filter.mp hν
    have hn:d∉exponentOrbit ν:=by
      intro hv
      exact hne (dominant_orbit_unique μ ν hμ hν (exponentOrbit_trans hd (exponentOrbit_symm hv)))
    rw [ite_eq_right hn,mul_zero]
  · intro h
    have hh:p.coeff μ=0:=by
      by_contra hh
      exact h (Finset.mem_filter.mpr ⟨MvPolynomial.mem_support_iff.mpr hh,hμ⟩)
    rw [hh,zero_mul]
end
end ElementaryPositivity.OrbitMonomial

end

end OAI
