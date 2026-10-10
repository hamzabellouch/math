import OAI.Combinatorics.PolynomialVacuum.Algebra.LagrangeDegree

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def killSite {ι : Type*} (j : ι) : MvPolynomial ι ℂ →+* MvPolynomial ι ℂ :=
  eval₂Hom C (fun i => if i=j then 0 else X i)

@[simp] theorem killSite_C {ι : Type*} (j : ι) (c : ℂ) : killSite j (C c)=C c := by
  simp [killSite]
@[simp] theorem killSite_X {ι : Type*} (i j : ι) : killSite j (X i)=if i=j then 0 else X i := by
  simp [killSite]

theorem killSite_rename_injective {ι κ : Type*} (f : ι → κ) (hf : Function.Injective f)
    (j : ι) (p : MvPolynomial ι ℂ) :
    killSite (f j) (rename f p)=rename f (killSite j p) := by
  have he : (killSite (f j)).comp (rename f).toRingHom =
      (rename f).toRingHom.comp (killSite j) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,rename_X,killSite_X]
      by_cases h : i=j
      · simp [h]
      · simp [h,hf.ne h]
  exact congrArg (fun g : MvPolynomial ι ℂ →+* MvPolynomial κ ℂ => g p) he

theorem killSite_rename {m : ℕ} (j : Fin m) (p : MvPolynomial (Fin m) ℂ) :
    killSite j.castSucc (rename Fin.castSucc p)=rename Fin.castSucc (killSite j p) :=
  killSite_rename_injective Fin.castSucc (Fin.castSucc_injective _) j p

theorem killSite_difference_ne_zero {m : ℕ} (j : Fin m) {i k : Fin m} (hik : i≠k) :
    killSite j (X i-X k)≠0 := by
  rw [map_sub,killSite_X,killSite_X]
  by_cases hi : i=j
  · subst i
    simp only [ite_true,ite_eq_right (Ne.symm hik),zero_sub,neg_ne_zero]
    exact X_ne_zero k
  · by_cases hk : k=j
    · subst k
      simp only [ite_eq_right hi,ite_true,sub_zero]
      exact X_ne_zero i
    · simp only [ite_eq_right hi,ite_eq_right hk]
      exact sub_ne_zero.mpr (fun h => hik (X_injective h))

theorem killSite_denominators_ne_zero {m : ℕ} (j : Fin m) :
    killSite j (allNodeDenominators m)≠0 := by
  simp only [allNodeDenominators,nodeDenominator,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact killSite_difference_ne_zero j (Ne.symm (Finset.mem_erase.mp hk).1)

 

theorem canonicalInterpolant_killSite {n : ℕ}
    (V : Fin (n+1) → MvPolynomial (Fin (n+1)) ℂ) (hV : CollisionCompatible V)
    (j : Fin (n+1)) (hz : ∀ i, killSite j (V i)=0) :
    killSite j.castSucc (reinsertLast (canonicalInterpolant V))=0 := by
  have h := congrArg (fun p => killSite j.castSucc (reinsertLast p))
    (canonicalInterpolant_cleared V hV)
  have he (p r : Polynomial (MvPolynomial (Fin (n+1)) ℂ)) :
      reinsertLast (p+r)=reinsertLast p+reinsertLast r := by simp [reinsertLast,Polynomial.eval₂_add]
  have hs (f : Fin (n+1) → Polynomial (MvPolynomial (Fin (n+1)) ℂ)) :
      reinsertLast (∑ i, f i)=∑ i, reinsertLast (f i) := by simp [reinsertLast,Polynomial.eval₂_finsetSum]
  simp only [reinsertLast_mul,reinsertLast_C,hs,map_mul,map_sum,killSite_rename,map_mul,hz,mul_zero,
    map_zero,zero_mul,Finset.sum_const_zero] at h
  have hn : rename Fin.castSucc (killSite j (allNodeDenominators (n+1)))≠0 := by
    intro h0
    exact killSite_denominators_ne_zero j ((rename_injective Fin.castSucc (Fin.castSucc_injective _)) (by simpa using h0))
  exact (mul_eq_zero.mp h).resolve_left hn

@[simp] theorem eval_killSite {ι : Type*} (j : ι) (Y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    eval Y (killSite j p)=eval (Function.update Y j 0) p := by
  change eval Y (eval₂ C (fun i => if i=j then 0 else X i) p)=_
  rw [eval_eval₂]
  have he : (eval Y).comp C=RingHom.id ℂ := by ext c; simp
  rw [he]
  change eval (fun i => eval Y (if i=j then 0 else X i)) p=_
  congr 2
  funext i
  simp only [Function.update_apply]
  split_ifs <;> simp

end PolynomialVacuumAlgebra

end OAI
