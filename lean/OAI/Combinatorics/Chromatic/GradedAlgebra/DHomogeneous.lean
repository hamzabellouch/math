import Mathlib
import OAI.Combinatorics.Chromatic.Walls.Taylor
import OAI.Combinatorics.Chromatic.GradedAlgebra.DegreeSet

namespace OAI

section
namespace ElementaryPositivity.CommonTranslation
open MvPolynomial
open ElementaryPositivity.Homogeneity
variable {σ : Type*} [Fintype σ]

lemma D_homogeneous (p : MvPolynomial σ ℚ) (k : ℤ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) :
    (D p).IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-1) := by
  classical
  rw [D_eq_sum]
  rw [show (∑ i : σ, pderiv i) p = ∑ i : σ,pderiv i p from by
    simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom (fun i : σ=>pderiv i) Finset.univ) p]
  exact IsWeightedHomogeneous.sum _ _ _ (fun i _=>hp.pderiv (by omega))

lemma taylor_coeff_homogeneous (p : MvPolynomial σ ℚ) (k : ℤ)
    (hp : p.IsWeightedHomogeneous (fun _=>(1:ℤ)) k) (n : ℕ) :
    ((taylor p).coeff n).IsWeightedHomogeneous (fun _=>(1:ℤ)) (k-n) := by
  induction n generalizing p k with
  | zero => simpa using hp
  | succ n ih =>
    have h := congrArg (fun q : Polynomial (MvPolynomial σ ℚ)=>q.coeff n) (taylor_derivative p)
    rw [Polynomial.coeff_derivative] at h
    have hh := ih (D p) (k-1) (D_homogeneous p k hp)
    have hom : ((n+1 : ℕ) : MvPolynomial σ ℚ).IsWeightedHomogeneous (fun _=>(1:ℤ)) 0 := by
      simpa using isWeightedHomogeneous_C (fun _ : σ=>(1:ℤ)) ((n+1:ℕ):ℚ)
    have hn : ((n+1 : ℕ) : MvPolynomial σ ℚ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have hm : (((n+1:ℕ):MvPolynomial σ ℚ) * (taylor p).coeff (n+1)).IsWeightedHomogeneous
        (fun _=>(1:ℤ)) (k-1-n) := by
      rw [mul_comm,Nat.cast_add,Nat.cast_one,h]
      exact hh
    have result := Homogeneity.of_mul _ _ hom hn hm
    have he : k-1-(n:ℤ)-0 = k-((n+1:ℕ):ℤ) := by push_cast; ring
    rwa [he] at result

end ElementaryPositivity.CommonTranslation

end

end OAI
