import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSurface

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def cupFactor (i k : ℕ) : MvPolynomial ℕ ℂ := X k-C T*X i

theorem substitution_factor_dvd (a b : ℕ) (p : MvPolynomial ℕ ℂ) :
    cupFactor a b ∣ p-cupSpecialize a b p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p r hp hr =>
    rw [map_add,show p+r-(cupSpecialize a b p+cupSpecialize a b r)=
      (p-cupSpecialize a b p)+(r-cupSpecialize a b r) by ring]
    exact dvd_add hp hr
  | mul_X p i hp =>
    rw [map_mul]
    have hx : cupFactor a b ∣ X i-cupSpecialize a b (X i) := by
      by_cases hi : i=b
      · subst i; simp [cupFactor]
      · simp [hi]
    rw [show p*X i-cupSpecialize a b p*cupSpecialize a b (X i)=
      (p-cupSpecialize a b p)*X i+cupSpecialize a b p*(X i-cupSpecialize a b (X i)) by ring]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hx _)

theorem cupFactor_dvd_of_specialize_zero (a b : ℕ) (p : MvPolynomial ℕ ℂ)
    (h : cupSpecialize a b p=0) : cupFactor a b ∣ p := by
  simpa only [h,sub_zero] using substitution_factor_dvd a b p

theorem X_sub_scaled_X_ne_zero {i j : ℕ} (hij : i≠j) (c : ℂ) :
    (X i-C c*X j : MvPolynomial ℕ ℂ)≠0 := by
  intro h
  have he := congrArg (eval (fun k : ℕ => if k=i then (1:ℂ) else 0)) h
  simp [Ne.symm hij] at he

theorem cupFactor_ne_zero {a b : ℕ} (hab : a<b) : cupFactor a b≠0 :=
  X_sub_scaled_X_ne_zero (by omega) T

theorem cupSpecialize_cupFactor_ne_zero {a b i k : ℕ} (hab : a<b) (hik : i < k)
    (hne : (i,k)≠(a,b)) : cupSpecialize a b (cupFactor i k)≠0 := by
  simp only [cupFactor,map_sub,map_mul,cupSpecialize_X,cupSpecialize_C]
  by_cases hk : k=b
  · subst k
    have hi : i≠b := by omega
    have hia : i≠a := by intro he; exact hne (Prod.ext he rfl)
    simp only [ite_true,ite_eq_right hi]
    rw [show C T*X a-C T*X i=(C T)*(X a-X i) by ring]
    exact mul_ne_zero (C_ne_zero.mpr T_ne_zero) (sub_ne_zero.mpr (fun he => hia (X_injective he).symm))
  · simp only [ite_eq_right hk]
    by_cases hi : i=b
    · subst i
      simp only [ite_true]
      rw [← mul_assoc,← map_mul]
      exact X_sub_scaled_X_ne_zero (by omega) (T*T)
    · simp only [ite_eq_right hi]
      exact X_sub_scaled_X_ne_zero (by omega) T

theorem cupProduct_dvd (S : Finset (ℕ × ℕ))
    (hs : ∀ ab∈S, ab.1<ab.2) (p : MvPolynomial ℕ ℂ)
    (hz : ∀ ab∈S, cupSpecialize ab.1 ab.2 p=0) :
    (∏ ab∈S, cupFactor ab.1 ab.2) ∣ p := by
  induction S using Finset.induction_on generalizing p with
  | empty => simp
  | @insert ab S hab ih =>
    have hab' := hs ab (Finset.mem_insert_self _ _)
    obtain ⟨r,hr⟩ := ih (fun cd h => hs cd (Finset.mem_insert_of_mem h)) p
      (fun cd h => hz cd (Finset.mem_insert_of_mem h))
    have hprod : cupSpecialize ab.1 ab.2 (∏ cd∈S, cupFactor cd.1 cd.2)≠0 := by
      rw [map_prod]
      apply Finset.prod_ne_zero_iff.mpr
      intro cd hcd
      apply cupSpecialize_cupFactor_ne_zero hab' (hs cd (Finset.mem_insert_of_mem hcd))
      intro he
      have he' : cd=ab := Prod.ext (congrArg Prod.fst he) (congrArg Prod.snd he)
      exact hab (he' ▸ hcd)
    have hr0 : cupSpecialize ab.1 ab.2 r=0 := by
      have hh := hz ab (Finset.mem_insert_self _ _)
      rw [hr,map_mul] at hh
      exact (mul_eq_zero.mp hh).resolve_left hprod
    obtain ⟨u,hu⟩ := cupFactor_dvd_of_specialize_zero ab.1 ab.2 r hr0
    refine ⟨u,?_⟩
    rw [Finset.prod_insert hab,hr,hu]
    ring

noncomputable def cupPairs (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range m) ×ˢ (Finset.range m)).filter (fun ab => ab.1<ab.2)
noncomputable def cupVandermonde (m : ℕ) : MvPolynomial ℕ ℂ :=
  ∏ ab∈cupPairs m, cupFactor ab.1 ab.2

@[simp] theorem mem_cupPairs (m i k : ℕ) : (i,k)∈cupPairs m ↔ i < k ∧ k < m := by
  simp only [cupPairs,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  omega

theorem cupVandermonde_ne_zero (m : ℕ) : cupVandermonde m≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro ab hab
  exact cupFactor_ne_zero ((mem_cupPairs _ _ _).mp hab).1

theorem cupVandermonde_dvd (m : ℕ) (p : MvPolynomial ℕ ℂ)
    (hz : ∀ i k, i < k → k < m → cupSpecialize i k p=0) : cupVandermonde m ∣ p := by
  apply cupProduct_dvd
  · intro ab hab; exact ((mem_cupPairs _ _ _).mp hab).1
  · intro ab hab
    obtain ⟨hi,hk⟩ := (mem_cupPairs _ _ _).mp hab
    exact hz _ _ hi hk

end PolynomialVacuumAlgebra

end OAI
