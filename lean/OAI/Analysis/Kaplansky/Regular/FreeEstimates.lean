import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Regular.RegularOperators

namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

lemma norm_disjoint_sum_le {E : Type*} [NormedAddCommGroup E] (T : ι → E) (P : ι → Prop)
    (hd : ∀ i j, P i → P j → i = j) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, if P i then T i else 0‖ ≤ c := by
  classical
  by_cases h : ∃ i, P i
  · obtain ⟨i,hi⟩ := h
    rw [Finset.sum_eq_single i]
    · simpa [hi] using hT i
    · intro j _ hji
      exact ite_eq_right (fun hj => hji (hd j i hj hi))
    · simp
  · simp only [not_exists] at h
    simpa [h] using hc

omit [CompleteSpace H] in
lemma cutSum_norm_le (e : ι → ℕ) (he : Function.Injective e)
    (T : ι → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c) (hT : ∀ i, ‖T i‖ ≤ c) :
    ‖∑ i, diagonal (T i) * negative (e i)‖ ≤ c := by
  classical
  let U (w : F2) : H →L[ℂ] H :=
    ∑ i, if Prefix (e i:ℤ) false (coordinate w) then T i else 0
  have hU (w : F2) : ‖U w‖ ≤ c := by
    apply norm_disjoint_sum_le _ _ _ hc hT
    intro i j hi hj
    exact he (Int.ofNat_inj.mp (prefix_disjoint hi hj).1)
  have heq : (∑ i, diagonal (T i) * negative (e i)) = lp.mapCLM 2 U hc hU := by
    ext x w
    change _ = (U w) (x w)
    simp only [sum_apply,lp.coeFn_sum,Finset.sum_apply]
    simp only [mul_apply_eq_comp,diagonal_apply,negative,mask_apply,U,sum_apply]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> simp
  rw [heq]
  exact lp.norm_mapCLM_le _ _ _ _

omit [CompleteSpace H] in
lemma sum_negative_norm_le (e : ι → ℕ) (he : Function.Injective e) :
    ‖∑ i, negative (H:=H) (e i)‖ ≤ 1 := by
  have h := cutSum_norm_le e he (fun _ => (1 : H →L[ℂ] H)) (by norm_num)
    (fun _ => ContinuousLinearMap.norm_id_le)
  simpa using h

omit [CompleteSpace H] in
lemma diagonal_creation_commute (T : H →L[ℂ] H) (n : ℕ) :
    Commute (diagonal T) (creation n) :=
  (diagonal_left_commute T _).mul_right
    ((Commute.one_right _).sub_right (diagonal_mask_commute T _))

lemma diagonal_starCreation_commute (T : H →L[ℂ] H) (n : ℕ) :
    Commute (diagonal T) (star (creation (H := H) n)) := by
  have h := (diagonal_creation_commute (star T) n).star_star
  simpa only [← diagonal_star,star_star] using h

lemma coeff_creation_star_mul (T S : H →L[ℂ] H) (m n : ℕ) :
    star (diagonal T * creation m) * (diagonal S * creation n) =
      diagonal (star T*S) * (star (creation (H := H) m) * creation n) := by
  simp only [star_mul,← diagonal_star,mul_assoc]
  rw [← mul_assoc (diagonal (star T)),← diagonal_mul,
    ← mul_assoc (star (creation (H := H) m)),(diagonal_starCreation_commute (star T*S) m).symm.eq,mul_assoc]

lemma creationSum_star_mul (e f : ι → ℕ) (T : ι → H →L[ℂ] H) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (f j)) =
      ∑ i, ∑ j, diagonal (star (T i)*T j)*(star (creation (H := H) (e i))*creation (f j)) := by
  rw [star_sum (R := HilbertSum F2 H →L[ℂ] HilbertSum F2 H)
    Finset.univ (fun index => diagonal (T index) * creation (e index))]
  simp only [Finset.sum_mul,Finset.mul_sum,coeff_creation_star_mul]
  rw [Finset.sum_comm]

lemma creationSum_gram_self (e : ι → ℕ) (he : Function.Injective e) (T : ι → H →L[ℂ] H)
    (hT : ∑ i, star (T i)*T i = 1) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (e j)) =
      1 - ∑ i, diagonal (star (T i)*T i)*negative (e i) := by
  classical
  rw [creationSum_star_mul]
  have hs (i : ι) : (∑ j, diagonal (star (T i)*T j)*(star (creation (H := H) (e i))*creation (e j))) =
      diagonal (star (T i)*T i)*(1-negative (e i)) := by
    rw [Finset.sum_eq_single i,creation_star_mul_self]
    · intro j _ hji
      rw [creation_orthogonal (fun h => hji (he h).symm),mul_zero]
    · simp
  simp_rw [hs,mul_sub,mul_one]
  rw [Finset.sum_sub_distrib]
  congr 1
  change (∑ i, diagonalHom (G:=F2) (H:=H) (star (T i)*T i)) = 1
  rw [← map_sum,hT,map_one]

lemma creationSum_gram_cross (e f : ι → ℕ) (hef : ∀ i j, e i ≠ f j) (T : ι → H →L[ℂ] H) :
    star (∑ i, diagonal (T i)*creation (e i)) * (∑ j, diagonal (T j)*creation (f j)) = 0 := by
  rw [creationSum_star_mul]
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  rw [creation_orthogonal (hef i j),mul_zero]


end KaplanskyConsequences.Regular

end

end OAI
