import Mathlib

namespace OAI

section
namespace ElementaryPositivity.Homogeneity
open MvPolynomial
variable {σ τ R : Type*} [CommRing R] {w : σ → ℤ}

lemma component_mul (p q : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous w m) (n : ℤ) :
    weightedHomogeneousComponent w (m+n) (p*q) =
      p * weightedHomogeneousComponent w n q := by
  classical
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  simp only [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hm := isWeightedHomogeneous_monomial w d (q.coeff d) rfl
  by_cases hn : Finsupp.weight w d = n
  · rw [hn] at hm
    rw [(hp.mul hm).weightedHomogeneousComponent_same,hm.weightedHomogeneousComponent_same]
  · rw [(hp.mul hm).weightedHomogeneousComponent_ne (m+n) (by omega),
      hm.weightedHomogeneousComponent_ne n (Ne.symm hn),mul_zero]

lemma of_mul [IsDomain R] (p q : MvPolynomial σ R) {m k : ℤ}
    (hp : p.IsWeightedHomogeneous w m) (hp0 : p≠0)
    (hpq : (p*q).IsWeightedHomogeneous w k) :
    q.IsWeightedHomogeneous w (k-m) := by
  have h : p * weightedHomogeneousComponent w (k-m) q = p*q := by
    rw [← component_mul p q hp,show m+(k-m)=k by omega,
      hpq.weightedHomogeneousComponent_same]
  have hh := mul_left_cancel₀ hp0 h
  rw [← hh]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

lemma constantWeight_rename (f : σ → τ) (p : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous (fun _=> (1:ℤ)) m) :
    (rename f p).IsWeightedHomogeneous (fun _=>(1:ℤ)) m := by
  classical
  rw [← p.support_sum_monomial_coeff,map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [rename_monomial]
  apply isWeightedHomogeneous_monomial
  have h := hp (mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one] at h ⊢
  exact (Finsupp.sum_mapDomain_index_addMonoidHom (f:=f) (s:=d)
    (fun _=> Nat.castAddMonoidHom ℤ)).trans h

lemma constantWeight_component_rename (f : σ → τ) (p : MvPolynomial σ R) (n : ℤ) :
    rename f (weightedHomogeneousComponent (fun _=>(1:ℤ)) n p) =
    weightedHomogeneousComponent (fun _=>(1:ℤ)) n (rename f p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hd := isWeightedHomogeneous_monomial (fun _ : σ=>(1:ℤ)) d c rfl
    have hrename := constantWeight_rename f (monomial d c) hd
    rw [weightedHomogeneousComponent_of_mem hd,
      weightedHomogeneousComponent_of_mem hrename]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]

noncomputable def degreeSet (p : MvPolynomial σ R) : Finset ℤ :=
  p.support.image (Finsupp.weight (fun _=>(1:ℤ)))

lemma sum_components (p : MvPolynomial σ R) :
    ∑ k ∈ degreeSet p, weightedHomogeneousComponent (fun _=>(1:ℤ)) k p = p := by
  classical
  ext d
  simp only [coeff_sum,coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (Finsupp.weight (fun _=>(1:ℤ)) d)]
  · simp
  · intro k hk hne
    rw [ite_eq_right (Ne.symm hne)]
  · intro hnot
    rw [ite_eq_left rfl]
    by_contra hne
    exact hnot (Finset.mem_image.mpr ⟨d,mem_support_iff.mpr hne,rfl⟩)

lemma homogeneous_negative_eq_zero (p : MvPolynomial σ R) {m : ℤ}
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) m) (hm : m<0) : p=0 := by
  apply hp.eq_zero_of_no_monomials
  intro d heq
  have hnn : (0:ℤ) ≤ Finsupp.weight (fun _=>(1:ℤ)) d := by
    simp only [Finsupp.weight_apply,nsmul_eq_mul,mul_one,Finsupp.sum]
    positivity
  omega

end ElementaryPositivity.Homogeneity

end

end OAI
