import OAI.Combinatorics.PolynomialVacuum.Algebra.LagrangeClearing

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem difference_degree_self {m : ℕ} {i k : Fin m} (hik : i≠k) :
    (X i-X k : MvPolynomial (Fin m) ℂ).degreeOf i=1 := by
  rw [sub_eq_add_neg,degreeOf_add_eq_of_degreeOf_lt]
  · simp
  · simp [degreeOf_X_of_ne hik]

theorem nodeDenominator_marked_degree {n : ℕ} (i : Fin (n+1)) :
    (nodeDenominator i).degreeOf i=n := by
  rw [nodeDenominator,degreeOf_prod_eq _ _]
  · have h (k) (hk : k ∈ Finset.univ.erase i) :
        (X i-X k : MvPolynomial (Fin (n+1)) ℂ).degreeOf i=1 :=
      difference_degree_self ((Finset.mem_erase.mp hk).1.symm)
    simp_rw [Finset.sum_congr rfl h]
    simp
  · intro k hk
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (X_injective h).symm)

theorem nodeDenominator_spectator_degree {n : ℕ} (i j : Fin (n+1)) (hji : j≠i) :
    (nodeDenominator i).degreeOf j=1 := by
  rw [nodeDenominator,degreeOf_prod_eq _ _]
  · rw [Finset.sum_eq_single j]
    · have he : (X i-X j : MvPolynomial (Fin (n+1)) ℂ)=-(X j-X i) := by ring
      rw [he,degreeOf_neg,difference_degree_self hji]
    · intro k hk hkj
      apply Nat.eq_zero_of_le_zero
      rw [sub_eq_add_neg]
      exact dadd (le_of_eq (degreeOf_X_of_ne hji)) (by simpa using
        (le_of_eq (degreeOf_X_of_ne hkj.symm) : (X k : MvPolynomial (Fin (n+1)) ℂ).degreeOf j≤0))
    · simp [hji]
  · intro k hk
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (X_injective h).symm)

theorem exceptNodeDenominator_ne_zero {m : ℕ} (i : Fin m) : exceptNodeDenominator i≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk; exact nodeDenominator_ne_zero k

@[simp] theorem reinsertLast_C {m : ℕ} (p : MvPolynomial (Fin m) ℂ) :
    reinsertLast (Polynomial.C p)=rename Fin.castSucc p := by simp [reinsertLast]
@[simp] theorem reinsertLast_mul {m : ℕ} (p r : Polynomial (MvPolynomial (Fin m) ℂ)) :
    reinsertLast (p*r)=reinsertLast p*reinsertLast r := by simp [reinsertLast,Polynomial.eval₂_mul]

theorem reinsert_nodeNumerator_degree {n : ℕ} (i j : Fin (n+1)) :
    (reinsertLast (nodeNumerator i)).degreeOf j.castSucc ≤ if i=j then 0 else 1 := by
  unfold nodeNumerator reinsertLast
  simp only [Polynomial.eval₂_finsetProd,Polynomial.eval₂_sub,Polynomial.eval₂_X,
    Polynomial.eval₂_C,AlgHom.toRingHom_eq_coe,RingHom.coe_coe,rename_X]
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.univ.erase i, if k=j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      have hz : (C T⁻¹*X (Fin.last (n+1)) : MvPolynomial (Fin (n+2)) ℂ).degreeOf j.castSucc≤0 :=
        dconst_mul _ (le_of_eq (degreeOf_X_of_ne (Fin.castSucc_ne_last j)))
      rw [sub_eq_add_neg]
      by_cases hkj : k=j
      · subst k
        simp only
        exact dadd (hz.trans (by omega)) (by simp)
      · simp only [ite_eq_right hkj]
        exact dadd hz (by rw [degreeOf_neg]; exact le_of_eq (degreeOf_X_of_ne (by
          intro h; exact hkj (Fin.castSucc_injective _ h.symm))))
    _ = if i=j then 0 else 1 := by
      by_cases h : i=j
      · subst i; simp
      · simp [h,Ne.symm h]

 

theorem canonicalInterpolant_spectator_degree {n : ℕ}
    (V : Fin (n+1) → MvPolynomial (Fin (n+1)) ℂ) (hV : CollisionCompatible V)
    (j : Fin (n+1)) (d : ℕ)
    (hmark : (V j).degreeOf j ≤ d+n)
    (hother : ∀ i, i≠j → (V i).degreeOf j ≤ d) :
    (reinsertLast (canonicalInterpolant V)).degreeOf j.castSucc ≤ d := by
  let p:=reinsertLast (canonicalInterpolant V)
  by_cases hp : p=0
  · simp only [← show p=reinsertLast (canonicalInterpolant V) from rfl,hp,degreeOf_zero,Nat.zero_le]
  have hcleared := congrArg (reinsertLast (m:=n+1)) (canonicalInterpolant_cleared V hV)
  have hsum : rename Fin.castSucc (allNodeDenominators (n+1))*p =
      ∑ i, rename Fin.castSucc (exceptNodeDenominator i*V i)*reinsertLast (nodeNumerator i) := by
    simpa only [p,reinsertLast,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C,AlgHom.toRingHom_eq_coe,RingHom.coe_coe] using hcleared
  have hD : rename Fin.castSucc (allNodeDenominators (n+1))≠0 := by
    exact fun h => allNodeDenominators_ne_zero (n+1) ((rename_injective Fin.castSucc (Fin.castSucc_injective _)) (by simpa using h))
  have hbound : (rename Fin.castSucc (allNodeDenominators (n+1))*p).degreeOf j.castSucc ≤
      (allNodeDenominators (n+1)).degreeOf j+d := by
    rw [hsum]
    apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro i hi
    have hf : (allNodeDenominators (n+1)).degreeOf j=
        (exceptNodeDenominator i).degreeOf j+(nodeDenominator i).degreeOf j := by
      rw [allNodeDenominators_factor i,degreeOf_mul_eq (exceptNodeDenominator_ne_zero i) (nodeDenominator_ne_zero i)]
    have hv : (rename Fin.castSucc (exceptNodeDenominator i*V i)).degreeOf j.castSucc ≤
        (exceptNodeDenominator i).degreeOf j+(V i).degreeOf j := by
      rw [degreeOf_rename_of_injective (Fin.castSucc_injective _)]
      exact degreeOf_mul_le _ _ _
    have hh:=dmul hv (reinsert_nodeNumerator_degree i j)
    by_cases hij : i=j
    · subst i
      rw [nodeDenominator_marked_degree] at hf
      simp only [ite_true,add_zero] at hh
      exact hh.trans (by omega)
    · rw [nodeDenominator_spectator_degree i j (Ne.symm hij)] at hf
      simp only [ite_eq_right hij] at hh
      exact hh.trans (by have ho:=hother i hij; omega)
  rw [degreeOf_mul_eq hD hp,degreeOf_rename_of_injective (Fin.castSucc_injective _)] at hbound
  change p.degreeOf j.castSucc ≤ d
  omega

end PolynomialVacuumAlgebra

end OAI
