import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialGenericity

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def cupSpecialize {ι : Type*} (a b : ι) :
    MvPolynomial ι ℂ →+* MvPolynomial ι ℂ :=
  eval₂Hom C (fun i => if i=b then C T*X a else X i)

@[simp] theorem cupSpecialize_C {ι : Type*} (a b : ι) (z : ℂ) :
    cupSpecialize a b (C z)=C z := by simp [cupSpecialize]
@[simp] theorem cupSpecialize_X {ι : Type*} (a b i : ι) :
    cupSpecialize a b (X i)=if i=b then C T*X a else X i := by simp [cupSpecialize]

@[simp] theorem eval_cupSpecialize {ι : Type*} (a b : ι) (Y : ι → ℂ) (p : MvPolynomial ι ℂ) :
    eval Y (cupSpecialize a b p)=eval (Function.update Y b (T*Y a)) p := by
  change eval Y (eval₂ C (fun i => if i=b then C T*X a else X i) p)=_
  rw [eval_eval₂]
  have hc : (eval Y).comp C=RingHom.id ℂ := by ext z; simp
  rw [hc]
  congr 2
  funext i
  split_ifs <;> simp_all

theorem T_ne_one : T≠1 := by
  intro h
  have hh := congrArg (fun z : ℂ => z^4) h
  norm_num [T,t,← pow_mul,q_pow_24] at hh

theorem cupSpecialize_X_ne_zero {ι : Type*} (a b i : ι) : cupSpecialize a b (X i)≠0 := by
  rw [cupSpecialize_X]
  split_ifs
  · exact mul_ne_zero (C_ne_zero.mpr T_ne_zero) (X_ne_zero a)
  · exact X_ne_zero i

theorem scaled_X_ne_X {ι : Type*} (a k : ι) : (C T*X a : MvPolynomial ι ℂ)≠X k := by
  by_cases h : k=a
  · subst k
    intro he
    have hh := congrArg (eval (fun _ => (1:ℂ))) he
    simp only [map_mul,eval_C,eval_X,mul_one] at hh
    exact T_ne_one hh
  · intro he
    have hh := congrArg (eval (fun i => if i=k then (1:ℂ) else 0)) he
    simp only [map_mul,eval_C,eval_X,ite_eq_right (Ne.symm h),ite_true,mul_zero] at hh
    exact zero_ne_one hh

theorem cupSpecialize_difference_ne_zero {ι : Type*} (a b : ι) {i j : ι}
    (hij : i≠j) : cupSpecialize a b (X i-X j)≠0 := by
  rw [map_sub,cupSpecialize_X,cupSpecialize_X,sub_ne_zero]
  by_cases hi : i=b
  · subst i
    simp only [ite_true,ite_eq_right (Ne.symm hij)]
    exact scaled_X_ne_X a j
  · by_cases hj : j=b
    · subst j
      simp only [ite_true,ite_eq_right hi]
      exact Ne.symm (scaled_X_ne_X a i)
    · simp only [ite_eq_right hi,ite_eq_right hj]
      exact fun h => hij (X_injective h)

noncomputable def distinctGuard {ι : Type*} (S : Finset ι) : MvPolynomial ι ℂ :=
  (∏ i ∈ S, X i) * ∏ i ∈ S, ∏ j ∈ S.erase i, (X i-X j)

theorem cupSpecialize_distinctGuard_ne_zero {ι : Type*} (a b : ι) (S : Finset ι) :
    cupSpecialize a b (distinctGuard S)≠0 := by
  simp only [distinctGuard,map_mul,map_prod]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => cupSpecialize_X_ne_zero a b i)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact cupSpecialize_difference_ne_zero a b (Ne.symm (Finset.mem_erase.mp hj).1)

theorem eval_distinctGuard_good {ι : Type*} (S : Finset ι) (Y : ι → ℂ)
    (h : eval Y (distinctGuard S)≠0) :
    (∀ i ∈ S, Y i≠0) ∧ Set.InjOn Y (S : Set ι) := by
  simp only [distinctGuard,map_mul,map_prod,map_sub,eval_X] at h
  obtain ⟨h0,h1⟩:=mul_ne_zero_iff.mp h
  refine ⟨fun i hi => Finset.prod_ne_zero_iff.mp h0 i hi,?_⟩
  intro i hi j hj he
  by_contra hij
  have hn := Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp h1 i hi) j
    (Finset.mem_erase.mpr ⟨Ne.symm hij,hj⟩)
  exact hn (sub_eq_zero.mpr he)

end PolynomialVacuumAlgebra

end OAI
