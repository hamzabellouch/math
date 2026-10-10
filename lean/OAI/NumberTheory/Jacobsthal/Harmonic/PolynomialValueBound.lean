import OAI.NumberTheory.Jacobsthal.Estimates.BivariateMonomialIndex

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem exponent_sum {D : ℕ} (i : MonomialIndex D) :
    (exponent i).sum (fun _ n => n) = i.1.val := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [Fin.sum_univ_two,exponent_zero,exponent_one]
  have h := i.2.isLt
  omega

noncomputable def encode {D : ℕ} (v : MonomialIndex D → ℤ) : MvPolynomial (Fin 2) ℤ :=
  ∑ i, MvPolynomial.monomial (exponent i) (v i)

theorem coeff_encode {D : ℕ} (v : MonomialIndex D → ℤ) (i : MonomialIndex D) :
    (encode v).coeff (exponent i) = v i := by
  classical
  simp [encode,MvPolynomial.coeff_monomial,(exponent_injective D).eq_iff]

theorem encode_eq_zero_iff {D : ℕ} (v : MonomialIndex D → ℤ) : encode v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun P : MvPolynomial (Fin 2) ℤ => P.coeff (exponent i)) h
    simpa only [coeff_encode,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Pi.zero_apply] using hi
  · rintro rfl
    simp [encode]

theorem encode_degree_le {D : ℕ} (v : MonomialIndex D → ℤ) : (encode v).totalDegree ≤ D := by
  apply (MvPolynomial.mem_restrictTotalDegree (R := ℤ) (Fin 2) D (encode v)).mp
  apply Submodule.sum_mem
  intro i hi
  apply (MvPolynomial.mem_restrictTotalDegree (R := ℤ) (Fin 2) D _).mpr
  have h := MvPolynomial.totalDegree_monomial_le (exponent i) (v i)
  change (MvPolynomial.monomial (exponent i) (v i)).totalDegree ≤ (exponent i).sum (fun _ n => n) at h
  rw [exponent_sum] at h
  exact h.trans (Nat.le_of_lt_succ i.1.isLt)

theorem encode_coefficient_bound {D H : ℕ} (v : MonomialIndex D → ℤ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) (m : Fin 2 →₀ ℕ) : |(encode v).coeff m| ≤ (H : ℤ) := by
  classical
  by_cases hm : ∃ i : MonomialIndex D, exponent i = m
  · obtain ⟨i,rfl⟩ := hm
    rw [coeff_encode]
    exact hv i
  · have hz : (encode v).coeff m = 0 := by
      simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro i hi
      exact ite_eq_right (fun h => hm ⟨i,h⟩)
    rw [hz,abs_zero]
    exact Int.natCast_nonneg H

noncomputable def encodeHom (D : ℕ) : (MonomialIndex D → ℤ) →+ MvPolynomial (Fin 2) ℤ where
  toFun := encode
  map_zero' := by simp [encode]
  map_add' v w := by simp [encode,Finset.sum_add_distrib]

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

theorem exponent_representation (D : ℕ) (m : Fin 2 →₀ ℕ)
    (hm : m.sum (fun _ n => n) ≤ D) : ∃ i : MonomialIndex D, exponent i = m := by
  have hsum : m.sum (fun _ n => n) = m 0+m 1 := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact Fin.sum_univ_two _
  rw [hsum] at hm
  let k : Fin (D+1) := ⟨m 0+m 1,by omega⟩
  have hj : m 0 < k.val+1 := by
    change m 0 < m 0+m 1+1
    omega
  let i : MonomialIndex D := ⟨k,⟨m 0,hj⟩⟩
  refine ⟨i,?_⟩
  ext j
  fin_cases j <;> simp [exponent,i,k]

theorem coeff_encode_of_not_range {D : ℕ} (v : MonomialIndex D → ℤ) (m : Fin 2 →₀ ℕ)
    (hm : ¬∃ i : MonomialIndex D, exponent i = m) : (encode v).coeff m = 0 := by
  classical
  simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hm ⟨i,h⟩)

theorem encode_coefficients (Q : MvPolynomial (Fin 2) ℤ) (D : ℕ) (hD : Q.totalDegree ≤ D) :
    encode (fun i : MonomialIndex D => Q.coeff (exponent i)) = Q := by
  classical
  ext m
  by_cases hm : ∃ i : MonomialIndex D, exponent i = m
  · obtain ⟨i,rfl⟩ := hm
    exact coeff_encode _ i
  · have hz : Q.coeff m = 0 := by
      by_contra hc
      have hd := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
      exact hm (exponent_representation D m (hd.trans hD))
    rw [coeff_encode_of_not_range _ m hm,hz]

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

noncomputable def evalReal (Q : MvPolynomial (Fin 2) ℤ) (x y : ℝ) : ℝ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℝ) ![x,y] Q

theorem evalReal_monomial {D : ℕ} (i : MonomialIndex D) (c : ℤ) (x y : ℝ) :
    evalReal (MvPolynomial.monomial (exponent i) c) x y =
      (c : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val)) := by
  change MvPolynomial.eval₂ (Int.castRingHom ℝ) ![x,y]
    (MvPolynomial.monomial (exponent i) c) = _
  rw [MvPolynomial.eval₂_monomial,Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [exponent,Fin.prod_univ_two]

theorem evalReal_encode {D : ℕ} (v : MonomialIndex D → ℤ) (x y : ℝ) :
    evalReal (encode v) x y =
      ∑ i : MonomialIndex D, (v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val)) := by
  change (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) ![x,y])
    (∑ i, MvPolynomial.monomial (exponent i) (v i)) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => evalReal_monomial i (v i) x y)

theorem evalReal_int (Q : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    evalReal Q (x : ℝ) (y : ℝ) = (MvPolynomial.eval ![x,y] Q : ℝ) := by
  have he : (Int.castRingHom ℝ) ∘ (![x,y] : Fin 2 → ℤ) = ![(x : ℝ),(y : ℝ)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.eval₂_comp (Int.castRingHom ℝ) ![x,y] Q
  rw [he] at h
  exact h.symm

theorem evalReal_encode_bound {D H : ℕ} (v : MonomialIndex D → ℤ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) (S x y : ℝ)
    (hx : 0 ≤ x ∧ x ≤ S) (hy : 0 ≤ y ∧ y ≤ S) :
    |evalReal (encode v) x y| ≤ ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by
  have hx0 := hx.1
  have hy0 := hy.1
  let M := max 1 S
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hxM : x ≤ M := hx.2.trans (le_max_right _ _)
  have hyM : y ≤ M := hy.2.trans (le_max_right _ _)
  have hterm (i : MonomialIndex D) :
      |(v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val))| ≤ (H : ℝ)*M^D := by
    have hc : |(v i : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hv i
    have hp : x^i.2.val*y^(i.1.val-i.2.val) ≤ M^D := by
      calc
        _ ≤ M^i.2.val*M^(i.1.val-i.2.val) := by gcongr
        _ = M^i.1.val := by
          rw [← pow_add]
          congr 1
          have hi := i.2.isLt
          omega
        _ ≤ M^D := pow_le_pow_right₀ hM (Nat.le_of_lt_succ i.1.isLt)
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hx.1 _),abs_of_nonneg (pow_nonneg hy.1 _)]
    exact mul_le_mul hc hp (mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg hy.1 _)) (Nat.cast_nonneg H)
  rw [evalReal_encode]
  calc
    _ ≤ ∑ i : MonomialIndex D, |(v i : ℝ)*(x^i.2.val*y^(i.1.val-i.2.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : MonomialIndex D, (H : ℝ)*M^D := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card (MonomialIndex D) : ℝ)*((H : ℝ)*M^D) := by simp
    _ = ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by rw [monomialIndex_card]; ring

theorem polynomial_value_bound (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ))
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) :
    |(MvPolynomial.eval ![x,y] Q : ℝ)| ≤ ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D := by
  rw [← evalReal_int,← encode_coefficients Q D hD]
  exact evalReal_encode_bound _ (fun i => hH (exponent i)) S x y hx hy

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI
