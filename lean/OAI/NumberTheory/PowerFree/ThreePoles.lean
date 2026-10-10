import OAI.NumberTheory.PowerFree.PoleCoefficients

namespace OAI

namespace QuarticPowerFree

section
open Polynomial
open scoped BigOperators Classical

theorem linearIndependent_of_fin_top_blocks {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (M : ℕ) (ι : Fin (M+1) → Type*) [∀ m, Fintype (ι m)]
    (p : ∀ m, ι m → V) (φ : ℕ → V →ₗ[K] W)
    (hzero : ∀ m i n, m.val < n → φ n (p m i) = 0)
    (hlead : ∀ m, LinearIndependent K (fun i => φ m.val (p m i))) :
    LinearIndependent K (fun i : Σ m, ι m => p i.1 i.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hci
  let s := Finset.univ.filter (fun m => ∃ j, c ⟨m,j⟩ ≠ 0)
  have hs : s.Nonempty := ⟨i.1,by simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨i.2,hci⟩⟩
  obtain ⟨m,hms,hmax⟩ := Finset.exists_max_image s (fun m => m.val) hs
  obtain ⟨j,hcj⟩ := (Finset.mem_filter.mp hms).2
  have hh := congrArg (φ m.val) hc
  simp only [map_sum,map_smul,map_zero] at hh
  rw [Fintype.sum_sigma,Finset.sum_eq_single m] at hh
  · exact hcj (Fintype.linearIndependent_iff.mp (hlead m) _ hh j)
  · intro n _ hnm
    by_cases hn : ∃ j, c ⟨n,j⟩ ≠ 0
    · have hle := hmax n (by simp [s,hn])
      have hlt : n.val < m.val := lt_of_le_of_ne hle (fun h => hnm (Fin.ext h))
      simp only [hzero n _ _ hlt,smul_zero,Finset.sum_const_zero]
    · push Not at hn
      simp only [hn,zero_smul,Finset.sum_const_zero]
  · simp

noncomputable def threePoleClearing {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (M m : ℕ) : Polynomial K :=
  (X-C r₀)^(2*(M-m))*(X-C (r 0))^(2*(M-m))*(X-C (r 1))^(2*(M-m))

noncomputable def threePolePolynomial {K : Type*} [Field K]
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (M m N : ℕ)
    (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) : Polynomial (Polynomial K) :=
  i.elim
    (fun a => C (threePoleClearing r₀ r M m * (X^a.val*threePoleBase r m)) * (X-C (C θ₀))^m)
    (fun j => C (threePoleClearing r₀ r M m * threePoleNumerator r₀ r m j) *
      ((X-C (C θ₀))^(m-(j.2.1.val+1))*(X-C (C (θ j.1)))^(j.2.1.val+1)))

lemma threePolePolynomial_degree {K : Type*} [Field K] (r₀ θ₀ : K)
    (r θ : Fin 2 → K) (M m N : ℕ) (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) :
    (threePolePolynomial r₀ θ₀ r θ M m N i).natDegree ≤ m := by
  cases i with
  | inl a =>
    apply (natDegree_C_mul_le _ _).trans
    simp
  | inr j =>
    apply (natDegree_C_mul_le _ _).trans
    apply natDegree_mul_le.trans
    simp only [natDegree_pow,natDegree_X_sub_C,mul_one]
    have := j.2.1.isLt
    omega

lemma threePolePolynomial_coeff {K : Type*} [Field K] (r₀ θ₀ : K)
    (r θ : Fin 2 → K) (M m N : ℕ) (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) :
    (threePolePolynomial r₀ θ₀ r θ M m N i).coeff m =
      threePoleClearing r₀ r M m *
        Sum.elim (fun a : Fin N => X^a.val*threePoleBase r m) (threePoleNumerator r₀ r m) i := by
  cases i with
  | inl a =>
    simp only [threePolePolynomial,Sum.elim_inl,coeff_C_mul]
    have hh : ((X-C (C θ₀))^m : Polynomial (Polynomial K)).coeff m = 1 := by
      have h1 : (X-C (C θ₀) : Polynomial (Polynomial K)).coeff 1 = 1 := by simp
      have h := coeff_pow_of_natDegree_le (m := m) (n := 1)
        (p := (X-C (C θ₀) : Polynomial (Polynomial K))) (by simp)
      rw [mul_one,h1,one_pow] at h
      exact h
    rw [hh,mul_one]
  | inr j =>
    simp only [threePolePolynomial,Sum.elim_inr,coeff_C_mul]
    have hj : m-(j.2.1.val+1)+(j.2.1.val+1) = m := by have := j.2.1.isLt; omega
    have hh₀ : ((X-C (C θ₀))^(m-(j.2.1.val+1)) : Polynomial (Polynomial K)).coeff
        (m-(j.2.1.val+1)) = 1 := by
      have h1 : (X-C (C θ₀) : Polynomial (Polynomial K)).coeff 1 = 1 := by simp
      have h := coeff_pow_of_natDegree_le (m := m-(j.2.1.val+1)) (n := 1)
        (p := (X-C (C θ₀) : Polynomial (Polynomial K))) (by simp)
      rw [mul_one,h1,one_pow] at h
      exact h
    have hh₁ : ((X-C (C (θ j.1)))^(j.2.1.val+1) : Polynomial (Polynomial K)).coeff
        (j.2.1.val+1) = 1 := by
      have h1 : (X-C (C (θ j.1)) : Polynomial (Polynomial K)).coeff 1 = 1 := by simp
      have h := coeff_pow_of_natDegree_le (m := j.2.1.val+1) (n := 1)
        (p := (X-C (C (θ j.1)) : Polynomial (Polynomial K))) (by simp)
      rw [mul_one,h1,one_pow] at h
      exact h
    have hh : (((X-C (C θ₀))^(m-(j.2.1.val+1)))*
        (X-C (C (θ j.1)))^(j.2.1.val+1) : Polynomial (Polynomial K)).coeff m = 1 := by
      calc
        _ = (((X-C (C θ₀))^(m-(j.2.1.val+1)))*
            (X-C (C (θ j.1)))^(j.2.1.val+1) : Polynomial (Polynomial K)).coeff
              ((m-(j.2.1.val+1))+(j.2.1.val+1)) := congrArg _ hj.symm
        _ = _ := coeff_mul_add_eq_of_natDegree_le (by simp) (by simp)
        _ = 1 := by rw [hh₀,hh₁,one_mul]
    rw [hh,mul_one]

theorem threePole_polynomials_independent {K : Type*} [Field K] (r₀ θ₀ : K)
    (r θ : Fin 2 → K) (h₀ : ∀ i, r i ≠ r₀) (hr : Function.Injective r)
    (M : ℕ) (N : Fin (M+1) → ℕ) :
    LinearIndependent K (fun i : Σ m : Fin (M+1), (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2) =>
      threePolePolynomial r₀ θ₀ r θ M i.1.val (N i.1) i.2) := by
  let ι := fun m : Fin (M+1) => (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2)
  let p := fun (m : Fin (M+1)) => threePolePolynomial r₀ θ₀ r θ M m.val (N m)
  let φ := fun m => (Polynomial.lcoeff (Polynomial K) m).restrictScalars K
  change LinearIndependent K (fun i : Σ m, ι m => p i.1 i.2)
  refine linearIndependent_of_fin_top_blocks M ι p φ ?_ ?_
  · intro m i n hmn
    exact coeff_eq_zero_of_natDegree_lt ((threePolePolynomial_degree r₀ θ₀ r θ M m.val (N m) i).trans_lt hmn)
  · intro m
    have hb := threePole_leading_independent r₀ r h₀ hr m.val (N m)
    have hH : threePoleClearing r₀ r M m.val ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (pow_ne_zero _ (X_sub_C_ne_zero _))) (pow_ne_zero _ (X_sub_C_ne_zero _))
    have hi := hb.map' (LinearMap.mulLeft K (threePoleClearing r₀ r M m.val))
      (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hH))
    have heq : (fun i => φ m.val (p m i)) =
        (LinearMap.mulLeft K (threePoleClearing r₀ r M m.val)) ∘
          Sum.elim (fun a : Fin (N m) => X^a.val*threePoleBase r m) (threePoleNumerator r₀ r m.val) := by
      funext i
      exact threePolePolynomial_coeff r₀ θ₀ r θ M m.val (N m) i
    rw [heq]
    exact hi

noncomputable def bivarEvaluation {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (t q : L) : Polynomial (Polynomial K) →ₐ[K] L :=
  Polynomial.aevalTower (Polynomial.aeval t) q

lemma bivarEvaluation_C {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (t q : L) (p : Polynomial K) : bivarEvaluation t q (C p) = Polynomial.aeval t p := by
  exact Polynomial.aevalTower_C _ _ _

lemma bivarEvaluation_X {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (t q : L) : bivarEvaluation (K := K) t q X = q := by
  exact Polynomial.aevalTower_X _ _

theorem bivarEvaluation_injective {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (t q : L) (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t))) :
    Function.Injective (bivarEvaluation (K := K) t q) := by
  let e := (MvPolynomial.optionEquivLeft K PUnit).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K PUnit))
  have he : (bivarEvaluation t q).comp e.toAlgHom =
      MvPolynomial.aeval (fun o : Option PUnit => o.elim q (fun _ => t)) := by
    ext o
    cases o with
    | none => simp [e,bivarEvaluation,Polynomial.aevalTower_X]
    | some u =>
      simp only [e,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.trans_apply,
        MvPolynomial.optionEquivLeft_X_some,MvPolynomial.aeval_X,Option.elim_some]
      change (bivarEvaluation t q) (Polynomial.map (MvPolynomial.uniqueAlgEquiv K PUnit).toRingHom
        (C (MvPolynomial.X u))) = t
      rw [Polynomial.map_C,bivarEvaluation_C]
      change (Polynomial.aeval t) (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (MvPolynomial.X u)) = t
      rw [MvPolynomial.eval₂_X,Polynomial.aeval_X]
  intro P Q hPQ
  obtain ⟨p,rfl⟩ := e.surjective P
  obtain ⟨q',rfl⟩ := e.surjective Q
  apply congrArg e
  apply (algebraicIndependent_iff_injective_aeval.mp hi)
  change ((bivarEvaluation t q).comp e.toAlgHom) p = ((bivarEvaluation t q).comp e.toAlgHom) q' at hPQ
  rwa [he] at hPQ

theorem threePole_evaluations_independent {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (h₀ : ∀ i, r i ≠ r₀) (hr : Function.Injective r)
    (M : ℕ) (N : Fin (M+1) → ℕ) (t q : L)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t))) :
    LinearIndependent K (fun i : Σ m : Fin (M+1), (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2) =>
      bivarEvaluation t q (threePolePolynomial r₀ θ₀ r θ M i.1.val (N i.1) i.2)) := by
  exact (threePole_polynomials_independent r₀ θ₀ r θ h₀ hr M N).map'
    (bivarEvaluation t q).toLinearMap (LinearMap.ker_eq_bot.mpr (bivarEvaluation_injective t q hi))

end

lemma square_relation_power {R : Type*} [CommRing R] (a b c : R) (hc : a^2*b=c)
    (M j : ℕ) (hj : j ≤ M) : a^(2*M)*b^j = a^(2*(M-j))*c^j := by
  have he : 2*M = 2*(M-j)+2*j := by omega
  rw [he,pow_add]
  simp only [pow_mul]
  rw [mul_assoc,←mul_pow,hc]

lemma threePole_base_identity {R : Type*} [CommRing R] (a₀ a₁ a₂ b₀ c₀ t : R)
    (h₀ : a₀^2*b₀=c₀) (M m e : ℕ) (hm : m ≤ M) :
    (a₀^(2*M)*a₁^(2*M)*a₂^(2*M))*(t^e*b₀^m) =
      (a₀^(2*(M-m))*a₁^(2*(M-m))*a₂^(2*(M-m)))*
        (t^e*(a₁^(2*m)*a₂^(2*m)))*c₀^m := by
  have h0 := square_relation_power a₀ b₀ c₀ h₀ M m hm
  have he : 2*M = 2*(M-m)+2*m := by omega
  calc
    _ = (a₀^(2*M)*b₀^m)*t^e*a₁^(2*M)*a₂^(2*M) := by ring
    _ = _ := by rw [h0,he,pow_add,pow_add]; ring

lemma threePole_extra_identity {R : Type*} [CommRing R] (a₀ a₁ a₂ b₀ b₁ c₀ c₁ : R)
    (h₀ : a₀^2*b₀=c₀) (h₁ : a₁^2*b₁=c₁) (M m j e : ℕ) (hm : m ≤ M) (hj : j ≤ m) :
    (a₀^(2*M)*a₁^(2*M)*a₂^(2*M))*(b₀^(m-j)*b₁^j*a₁^e) =
      (a₀^(2*(M-m))*a₁^(2*(M-m))*a₂^(2*(M-m)))*
        (a₁^(2*(m-j)+e)*(a₀^(2*j)*a₂^(2*m)))*(c₀^(m-j)*c₁^j) := by
  have h0 := square_relation_power a₀ b₀ c₀ h₀ M (m-j) (by omega)
  have h1 := square_relation_power a₁ b₁ c₁ h₁ M j (by omega)
  have he₀ : 2*(M-(m-j)) = 2*(M-m)+2*j := by omega
  have he₁ : 2*(M-j) = 2*(M-m)+2*(m-j) := by omega
  have he₂ : 2*M = 2*(M-m)+2*m := by omega
  calc
    _ = (a₀^(2*M)*b₀^(m-j))*(a₁^(2*M)*b₁^j)*a₂^(2*M)*a₁^e := by ring
    _ = _ := by rw [h0,h1,he₀,he₁,he₂]; simp only [pow_add]; ring

open Polynomial
open scoped BigOperators Classical

noncomputable def threePoleFunction {L : Type*} [CommRing L]
    (t b₀ : L) (a b : Fin 2 → L) (m N : ℕ)
    (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) : L :=
  i.elim (fun j => t^j.val*b₀^m)
    (fun j => b₀^(m-(j.2.1.val+1))*b j.1^(j.2.1.val+1)*a j.1^j.2.2.val)

lemma threePole_evaluation_identity {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (t q b₀ : L) (b : Fin 2 → L)
    (h₀ : (t-algebraMap K L r₀)^2*b₀=q-algebraMap K L θ₀)
    (h : ∀ i, (t-algebraMap K L (r i))^2*b i=q-algebraMap K L (θ i))
    (M m N : ℕ) (hm : m ≤ M) (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) :
    bivarEvaluation t q (threePolePolynomial r₀ θ₀ r θ M m N i) =
      ((t-algebraMap K L r₀)^(2*M)*(t-algebraMap K L (r 0))^(2*M)*
        (t-algebraMap K L (r 1))^(2*M))*
      threePoleFunction t b₀ (fun i => t-algebraMap K L (r i)) b m N i := by
  cases i with
  | inl j =>
    simpa only [threePolePolynomial,threePoleFunction,Sum.elim_inl,threePoleClearing,
      threePoleBase,map_mul,map_pow,map_sub,bivarEvaluation_C,bivarEvaluation_X,
      Polynomial.aeval_X,Polynomial.aeval_C]
      using (threePole_base_identity (t-algebraMap K L r₀) (t-algebraMap K L (r 0))
        (t-algebraMap K L (r 1)) b₀ (q-algebraMap K L θ₀) t h₀ M m j.val hm).symm
  | inr j =>
    rcases j with ⟨s,j,e⟩
    have hj : j.val+1 ≤ m := by omega
    have hh := (threePole_extra_identity (t-algebraMap K L r₀) (t-algebraMap K L (r s))
      (t-algebraMap K L (r (1-s))) b₀ (b s) (q-algebraMap K L θ₀)
      (q-algebraMap K L (θ s)) h₀ (h s) M m (j.val+1) e.val hm hj).symm
    simp only [threePolePolynomial,threePoleFunction,Sum.elim_inr,threePoleClearing,
      threePoleNumerator,map_mul,map_pow,map_sub,bivarEvaluation_C,bivarEvaluation_X,
      Polynomial.aeval_X,Polynomial.aeval_C]
    fin_cases s
    all_goals norm_num at hh ⊢
    all_goals linear_combination hh

theorem threePole_functions_independent {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (hr₀ : ∀ i, r i ≠ r₀) (hr : Function.Injective r)
    (t q b₀ : L) (b : Fin 2 → L)
    (hi : AlgebraicIndependent K (fun o : Option PUnit => o.elim q (fun _ => t)))
    (h₀ : (t-algebraMap K L r₀)^2*b₀=q-algebraMap K L θ₀)
    (h : ∀ i, (t-algebraMap K L (r i))^2*b i=q-algebraMap K L (θ i))
    (M : ℕ) (N : Fin (M+1) → ℕ) :
    LinearIndependent K (fun i : Σ m : Fin (M+1), (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2) =>
      threePoleFunction t b₀ (fun i => t-algebraMap K L (r i)) b i.1.val (N i.1) i.2) := by
  let D := (t-algebraMap K L r₀)^(2*M)*(t-algebraMap K L (r 0))^(2*M)*
    (t-algebraMap K L (r 1))^(2*M)
  have he := threePole_evaluations_independent r₀ θ₀ r θ hr₀ hr M N t q hi
  have heq : (fun i : Σ m : Fin (M+1), (Fin (N m)) ⊕ (Fin 2 × Fin m.val × Fin 2) =>
      bivarEvaluation t q (threePolePolynomial r₀ θ₀ r θ M i.1.val (N i.1) i.2)) =
      (LinearMap.mulLeft K D) ∘ (fun i =>
        threePoleFunction t b₀ (fun i => t-algebraMap K L (r i)) b i.1.val (N i.1) i.2) := by
    funext i
    exact threePole_evaluation_identity r₀ θ₀ r θ t q b₀ b h₀ h M i.1.val (N i.1) (by omega) i.2
  rw [heq] at he
  exact LinearIndependent.of_comp (LinearMap.mulLeft K D) he

end QuarticPowerFree

end OAI
