import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusEmbedding
import OAI.Combinatorics.Chromatic.GradedAlgebra.MutationRootMap

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits Polynomial
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ)
lemma centeredPolynomial_degree_le (t : ℕ) : (centeredPolynomial v t).natDegree≤t := by
  unfold centeredPolynomial
  have H:=Polynomial.natDegree_prod_le Finset.univ
    (fun i : Fin t=>(1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X))
  have H' := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin t) _ =>
    natDegree_linear_le (↑(v^centeredExponent t i):K))
  exact H.trans (by simpa using H')
lemma centered_eval_ratio (t : ℕ) :
    (centeredPolynomial v t).eval₂ RatFunc.C
      (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)=(pureRatio v (t:ℤ):RatFunc K) := by
  change (Polynomial.eval₂RingHom RatFunc.C
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)) (centeredPolynomial v t)=_
  rw [centeredPolynomial,map_prod,pureRatio_nat_val,←Fin.prod_univ_eq_prod_range]
  change (∏i : Fin t, (1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X).eval₂ RatFunc.C
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X))=_
  have H (i : Fin t) :
      (1+Polynomial.C (↑(v^centeredExponent t i):K)*Polynomial.X).eval₂ RatFunc.C
        (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)=
      1+RatFunc.C (↑(v^(-2*((i.rev:ℕ):ℤ)-1)):K)*RatFunc.X := by
    simp only [Polynomial.eval₂_add,Polynomial.eval₂_one,Polynomial.eval₂_mul,
      Polynomial.eval₂_C,Polynomial.eval₂_X]
    rw [←mul_assoc,←map_mul,←Units.val_mul,←zpow_add]
    congr 4
    simp only [centeredExponent,Fin.val_rev]
    have H:=i.isLt
    congr 1
    omega
  simp_rw [H]
  exact Equiv.prod_comp Fin.revPerm
    (fun i : Fin t=>1+RatFunc.C (↑(v^(-2*((i:ℕ):ℤ)-1)):K)*RatFunc.X)

variable (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
include hΩ in
lemma complement_pairing (m : M) : complementAlpha k p Ω (off k p hp m)=Ω p m := by
  change Ω p (m-k m • p)=_
  rw [map_sub,map_zsmul,hΩ,smul_zero,sub_zero]
lemma centeredScalar_shift (n a j : ℤ) : centeredScalar v (n+j) a=
    centeredScalar v n a*(RatFunc.C (↑(v^(-a)):K)*RatFunc.X)^j := by
  have hz : (RatFunc.X:RatFunc K)≠0:=RatFunc.X_ne_zero
  rw [centeredScalar,centeredScalar,mul_zpow,←map_zpow₀,
    ←Units.val_zpow_eq_zpow_val,←zpow_mul,zpow_add₀ hz]
  rw [show -(n+j)*a= -n*a+(-a)*j by ring,zpow_add,Units.val_mul,map_mul]
  ring
include hΩ in
lemma embed_pure_row_term (m : M) (j : ℕ) (a : K) :
    embed v Ω hΩ k p hp (Torus.monomial v Ω (m+j • p) a)=
      FiberTorus.monomial v _ _ (off k p hp m)
        (centeredScalar v (k m) (Ω p m)*RatFunc.C a*
          (RatFunc.C (↑(v^(-Ω p m)):K)*RatFunc.X)^j) := by
  rw [embed_monomial]
  simp only [map_add,map_nsmul,hp,nsmul_eq_mul,mul_one,off_p,smul_zero,add_zero]
  rw [complement_pairing Ω hΩ k p hp m,centeredScalar_shift]
  rw [zpow_natCast]
  congr 1
  ring
include hΩ in
lemma pureAction_centered (m : M) (t : ℕ) (ht : Ω p m=(t:ℤ)) :
    pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
      (embed v Ω hΩ k p hp (Torus.X v Ω m))=
      embed v Ω hΩ k p hp (centeredCrossing v Ω p m t) := by
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp m,ht,←centered_eval_ratio]
  rw [centeredCrossing,map_sum]
  simp_rw [embed_pure_row_term v Ω hΩ k p hp,ht]
  have He := Polynomial.eval₂_eq_sum_range' RatFunc.C
    (Nat.lt_succ_of_le (centeredPolynomial_degree_le v t))
    (RatFunc.C (↑(v^(-(t:ℤ))):K)*RatFunc.X)
  rw [He,Finset.mul_sum]
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [FiberTorus.monomial,mul_assoc]
  classical
  exact (map_sum (Finsupp.singleAddHom (off k p hp m)) _ Finset.univ)
end
end ElementaryPositivity.RationalFiber

end

end OAI
