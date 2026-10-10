import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalRotation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def scalePolynomial {ι : Type*} (c : ℂ) : MvPolynomial ι ℂ →+* MvPolynomial ι ℂ :=
  eval₂Hom C (fun j => C c * X j)

theorem scalePolynomial_monomial {ι : Type*} (c : ℂ) (d : ι →₀ ℕ) (r : ℂ) :
    scalePolynomial c (monomial d r)=monomial d (c^d.degree*r) := by
  classical
  rw [scalePolynomial,eval₂Hom_monomial]
  simp only [Finsupp.prod,mul_pow,Finset.prod_mul_distrib,← map_pow,← map_prod]
  rw [Finset.prod_pow_eq_pow_sum,← Finsupp.degree_apply,monomial_eq]
  simp only [map_mul,Finsupp.prod]
  ring

theorem coeff_scalePolynomial {ι : Type*} (c : ℂ) (p : MvPolynomial ι ℂ) (d : ι →₀ ℕ) :
    (scalePolynomial c p).coeff d=c^d.degree*p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [scalePolynomial_monomial]
    by_cases h : e=d
    · subst e; simp
    · simp [coeff_monomial,h]
  | add p r hp hr => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hp,hr,mul_add]

theorem degreeOf_scalePolynomial_le {ι : Type*} (c : ℂ) (p : MvPolynomial ι ℂ) (j : ι) :
    (scalePolynomial c p).degreeOf j ≤ p.degreeOf j := by
  apply degreeOf_le_iff.mpr
  intro d hd
  apply degreeOf_le_iff.mp le_rfl d
  rw [mem_support_iff,coeff_scalePolynomial] at hd
  exact mem_support_iff.mpr ((mul_ne_zero_iff.mp hd).2)

theorem eval_scalePolynomial {ι : Type*} (c : ℂ) (p : MvPolynomial ι ℂ) (X : ι → ℂ) :
    eval X (scalePolynomial c p)=eval (fun j => c*X j) p := by
  change eval X (eval₂ C (fun j => C c * MvPolynomial.X j) p)=_
  rw [eval_eval₂]
  simp only [eval_C,map_mul,eval_X]
  have hC : (eval X).comp (C : ℂ →+* MvPolynomial ι ℂ)=RingHom.id ℂ := by ext; simp
  rw [hC]
  rfl

theorem killSite_scalePolynomial {ι : Type*} (c : ℂ) (p : MvPolynomial ι ℂ) (j : ι) :
    killSite j (scalePolynomial c p)=scalePolynomial c (killSite j p) := by
  have he : (killSite j).comp (scalePolynomial c)=(scalePolynomial c).comp (killSite j) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [scalePolynomial]
    · intro k
      simp only [RingHom.comp_apply,scalePolynomial,eval₂Hom_X',map_mul,killSite_C,killSite_X]
      split_ifs <;> simp [map_zero]
  exact congrArg (fun f : MvPolynomial ι ℂ →+* MvPolynomial ι ℂ => f p) he

theorem homogeneous_scale {ι : Type*} {p : MvPolynomial ι ℂ} {d : ℕ} (hp : p.IsHomogeneous d) (c : ℂ) :
    scalePolynomial c p=C (c^d)*p := by
  ext e
  rw [coeff_scalePolynomial,coeff_C_mul]
  by_cases h : p.coeff e=0
  · simp [h]
  · rw [show e.degree=d from by rw [Finsupp.degree_eq_weight_one]; exact hp h]

theorem homogeneous_of_scale_two {ι : Type*} (p : MvPolynomial ι ℂ) (d : ℕ)
    (hp : scalePolynomial 2 p=C ((2:ℂ)^d)*p) : p.IsHomogeneous d := by
  intro e he
  have hc := congrArg (fun polynomial : MvPolynomial ι ℂ => polynomial.coeff e) hp
  rw [coeff_scalePolynomial,coeff_C_mul] at hc
  have heq : (2:ℂ)^e.degree=(2:ℂ)^d := (mul_right_cancel₀ he hc)
  have hn : (2:ℕ)^e.degree=(2:ℕ)^d := by exact_mod_cast heq
  have hh : e.degree=d := (Nat.pow_right_injective (by omega : 2≤(2:ℕ))) hn
  rw [Finsupp.degree_eq_weight_one] at hh
  exact hh

end PolynomialVacuumAlgebra

end OAI
