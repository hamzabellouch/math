import OAI.Combinatorics.PolynomialVacuum.Algebra.CupDivisibility
import OAI.Combinatorics.PolynomialVacuum.Algebra.LagrangeDegree
import OAI.Combinatorics.PolynomialVacuum.Algebra.KillSite

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem cupFactor_degree {a b : ℕ} (hab : a<b) (j : ℕ) :
    (cupFactor a b).degreeOf j=if a=j ∨ b=j then 1 else 0 := by
  by_cases hja : a=j
  · subst a
    rw [ite_eq_left (Or.inl rfl),cupFactor,sub_eq_add_neg,add_comm,degreeOf_add_eq_of_degreeOf_lt]
    · rw [degreeOf_neg,degreeOf_C_mul _ _ (by simpa using T_ne_zero),degreeOf_X_self]
    · rw [degreeOf_X_of_ne (by omega),degreeOf_neg,degreeOf_C_mul _ _ (by simpa using T_ne_zero),degreeOf_X_self]
      omega
  · by_cases hjb : b=j
    · subst b
      rw [ite_eq_left (Or.inr rfl),cupFactor,sub_eq_add_neg,degreeOf_add_eq_of_degreeOf_lt]
      · exact degreeOf_X_self _
      · rw [degreeOf_neg,degreeOf_C_mul _ _ (by simpa using T_ne_zero),degreeOf_X_of_ne (by omega),degreeOf_X_self]
        omega
    · rw [ite_eq_right (by tauto)]
      apply Nat.eq_zero_of_le_zero
      apply (degreeOf_sub_le _ _ _).trans
      apply max_le
      · exact le_of_eq (degreeOf_X_of_ne (Ne.symm hjb))
      · exact dconst_mul _ (le_of_eq (degreeOf_X_of_ne (Ne.symm hja)))

theorem cupPairs_incident_card (m j : ℕ) (hj : j < m) :
    ((cupPairs m).filter (fun ab => ab.1=j ∨ ab.2=j)).card=m-1 := by
  have he : ((cupPairs m).filter (fun ab => ab.1=j ∨ ab.2=j)).card=
      ((Finset.range m).erase j).card := by
    apply Finset.card_bij (fun ab _ => if ab.1=j then ab.2 else ab.1)
    · intro ab hab
      obtain ⟨hab,hi⟩ := Finset.mem_filter.mp hab
      have ht := (mem_cupPairs _ _ _).mp hab
      simp only [Finset.mem_erase,Finset.mem_range]
      split_ifs <;> rcases hi with hi|hi <;> omega
    · intro ab hab cd hcd he
      obtain ⟨hab,hi⟩ := Finset.mem_filter.mp hab
      obtain ⟨hcd,hi'⟩ := Finset.mem_filter.mp hcd
      have ht := (mem_cupPairs _ _ _).mp hab
      have ht' := (mem_cupPairs _ _ _).mp hcd
      apply Prod.ext <;> split_ifs at he <;> rcases hi with hi|hi <;> rcases hi' with hi'|hi' <;> omega
    · intro k hk
      obtain ⟨hkj,hk⟩ := Finset.mem_erase.mp hk
      have hkm := Finset.mem_range.mp hk
      by_cases h : k<j
      · refine ⟨(k,j),?_,?_⟩
        · simp only [Finset.mem_filter,mem_cupPairs]; exact ⟨⟨h,hj⟩,Or.inr trivial⟩
        · simp [hkj]
      · refine ⟨(j,k),?_,?_⟩
        · simp only [Finset.mem_filter,mem_cupPairs]; exact ⟨⟨by omega,hkm⟩,Or.inl trivial⟩
        · simp
  rw [he,Finset.card_erase_of_mem (Finset.mem_range.mpr hj),Finset.card_range]

theorem cupVandermonde_degree (m j : ℕ) (hj : j < m) :
    (cupVandermonde m).degreeOf j=m-1 := by
  rw [cupVandermonde,degreeOf_prod_eq _ _]
  · have hterm (ab : ℕ × ℕ) (hab : ab∈cupPairs m) :
        (cupFactor ab.1 ab.2).degreeOf j=if ab.1=j ∨ ab.2=j then 1 else 0 :=
      cupFactor_degree ((mem_cupPairs _ _ _).mp hab).1 j
    rw [Finset.sum_congr rfl hterm,Finset.sum_boole]
    exact cupPairs_incident_card m j hj
  · intro ab hab; exact cupFactor_ne_zero ((mem_cupPairs _ _ _).mp hab).1

theorem killSite_cupFactor_ne_zero {a b : ℕ} (hab : a<b) (j : ℕ) :
    killSite j (cupFactor a b)≠0 := by
  simp only [cupFactor,map_sub,map_mul,killSite_X,killSite_C]
  by_cases ha : a=j
  · subst a
    simp only [ite_true,ite_eq_right (by omega : b≠j),mul_zero,sub_zero]
    exact X_ne_zero _
  · by_cases hb : b=j
    · subst b
      simp only [ite_true,ite_eq_right ha,zero_sub,neg_ne_zero]
      exact mul_ne_zero (C_ne_zero.mpr T_ne_zero) (X_ne_zero _)
    · simp only [ite_eq_right ha,ite_eq_right hb]
      exact cupFactor_ne_zero hab

theorem killSite_cupVandermonde_ne_zero (m j : ℕ) : killSite j (cupVandermonde m)≠0 := by
  rw [cupVandermonde,map_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro ab hab
  exact killSite_cupFactor_ne_zero ((mem_cupPairs _ _ _).mp hab).1 j

theorem cupQuotient_degree (m j d : ℕ) (hj : j < m) (p r : MvPolynomial ℕ ℂ)
    (he : p=cupVandermonde m*r) (hd : p.degreeOf j ≤ m-1+d) : r.degreeOf j ≤ d := by
  by_cases hr : r=0
  · simp [hr]
  rw [he,degreeOf_mul_eq (cupVandermonde_ne_zero m) hr,cupVandermonde_degree m j hj] at hd
  omega

theorem cupQuotient_minus_zero (m j : ℕ) (p r : MvPolynomial ℕ ℂ)
    (he : p=cupVandermonde m*r) (hz : killSite j p=0) : killSite j r=0 := by
  rw [he,map_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (killSite_cupVandermonde_ne_zero m j)

end PolynomialVacuumAlgebra

end OAI
