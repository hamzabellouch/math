import OAI.NumberTheory.SingleFold.DescentMap

namespace OAI

namespace SingleFold.SquareSupport

lemma squarefree_decomposition {x : ℚ} (hx : x ≠ 0) :
    ∃ (d : ℕ) (r : ℚ), 0 < d ∧ r ≠ 0 ∧ Squarefree d ∧ |x| = d*r^2 := by
  have hn : 0 < x.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hx)
  obtain ⟨d,k,hd,hk,he,hf⟩ := Nat.sq_mul_squarefree_of_pos (Nat.mul_pos hn x.den_pos)
  refine ⟨d,(k:ℚ)/x.den,hd,div_ne_zero (by exact_mod_cast hk.ne') (by exact_mod_cast x.den_ne_zero),hf,?_⟩
  have he' : (k:ℚ)^2*d=x.num.natAbs*x.den := by exact_mod_cast he
  rw [Rat.abs_def, Rat.divInt_eq_div]
  push_cast
  field_simp
  have habs : |(x.num:ℚ)| = (x.num.natAbs:ℚ) := by simp
  rw [habs]
  nlinarith only [he']

lemma val_add_eq {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hval : padicValRat p x ≠ padicValRat p y) :
    padicValRat p (x+y) = min (padicValRat p x) (padicValRat p y) := by
  apply padicValRat.add_eq_min _ hx hy hval
  intro h
  apply hval
  have he : x = -y := by linarith
  simp [he]

lemma even_val_triple {p : ℕ} [Fact p.Prime] {x y a b : ℚ}
    (hx : x ≠ 0) (hxa : x+a ≠ 0) (hxb : x+b ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hva : padicValRat p a = 0) (hvb : padicValRat p b = 0)
    (he : y^2=x*(x+a)*(x+b)) : Even (padicValRat p x) := by
  have hv := congrArg (padicValRat p) he
  rw [padicValRat.pow, padicValRat.mul (mul_ne_zero hx hxa) hxb,
    padicValRat.mul hx hxa] at hv
  by_cases hz : padicValRat p x=0
  · simp [hz]
  have h₁ := val_add_eq (p := p) hx ha (by simpa [hva] using hz)
  have h₂ := val_add_eq (p := p) hx hb (by simpa [hvb] using hz)
  rw [hva] at h₁
  rw [hvb] at h₂
  rcases lt_or_gt_of_ne hz with hl | hl
  · rw [min_eq_left hl.le] at h₁ h₂
    rw [h₁,h₂] at hv
    refine ⟨padicValRat p y - padicValRat p x, ?_⟩
    omega
  · rw [min_eq_right hl.le] at h₁ h₂
    rw [h₁,h₂] at hv
    exact ⟨padicValRat p y, by omega⟩

lemma squarefree_support {x r : ℚ} {d D : ℕ} (hd : 0 < d) (hr : r ≠ 0)
    (hf : Squarefree d) (he : |x| = d*r^2) (hD : D ≠ 0)
    (hv : ∀ p : ℕ, p.Prime → ¬p ∣ D → Even (padicValRat p x)) : d ∣ D := by
  apply (Nat.factorization_le_iff_dvd hd.ne' hD).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpd : p ∣ d
    · have hdd := Nat.factorization_eq_one_of_squarefree hf hp hpd
      have hpd' : p ∣ D := by
        by_contra hpD
        have : Fact p.Prime := ⟨hp⟩
        have hxval := congrArg (padicValRat p) he
        have habs : padicValRat p |x| = padicValRat p x := by
          rcases le_or_gt 0 x with hs | hs
          · rw [abs_of_nonneg hs]
          · rw [abs_of_neg hs, padicValRat.neg]
        rw [habs, padicValRat.mul (by exact_mod_cast hd.ne') (pow_ne_zero _ hr),
          padicValRat.of_nat, padicValRat.pow, ← Nat.factorization_def d hp, hdd] at hxval
        obtain ⟨k,hk⟩ := hv p hp hpD
        omega
      rw [hdd]
      exact (hp.dvd_iff_one_le_factorization hD).mp hpd'
    · simp [Nat.factorization_eq_zero_of_not_dvd hpd]
  · simp [Nat.factorization_eq_zero_of_not_prime d hp]

lemma supported_decomposition {x : ℚ} {D : ℕ} (hx : x ≠ 0) (hD : D ≠ 0)
    (hv : ∀ p : ℕ, p.Prime → ¬p ∣ D → Even (padicValRat p x)) :
    ∃ (d : ℕ) (r : ℚ), d ∣ D ∧ r ≠ 0 ∧ (x=d*r^2 ∨ x=-(d*r^2)) := by
  obtain ⟨d,r,hd,hr,hf,he⟩ := squarefree_decomposition hx
  refine ⟨d,r,squarefree_support hd hr hf he hD hv,hr,?_⟩
  rcases le_or_gt 0 x with hs | hs
  · exact Or.inl (by simpa [abs_of_nonneg hs] using he)
  · exact Or.inr (by rw [abs_of_neg hs] at he; linarith)

end SingleFold.SquareSupport

namespace SingleFold.Descent
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open SquareSupport

lemma supported_zero (P : E.Point) : ∃ (d : ℕ) (r : ℚ), d ∣ 5 ∧ r ≠ 0 ∧
    (alphaVal 0 P=d*r^2 ∨ alphaVal 0 P=-(d*r^2)) := by
  cases P with
  | zero => exact ⟨1,1,by norm_num,by norm_num,Or.inl (by norm_num [alphaVal])⟩
  | some x y h =>
    by_cases hx : x=0
    · exact ⟨1,5,by norm_num,by norm_num,Or.inr (by norm_num [alphaVal,adjusted,hx])⟩
    by_cases hx5 : x=5
    · exact ⟨5,1,by norm_num,by norm_num,Or.inl (by norm_num [alphaVal,adjusted,hx5])⟩
    by_cases hxm5 : x= -5
    · exact ⟨5,1,by norm_num,by norm_num,Or.inr (by norm_num [alphaVal,adjusted,hxm5])⟩
    simp only [alphaVal_some, sub_zero, adjusted, ite_eq_right hx]
    apply supported_decomposition hx (by norm_num)
    intro p hp hp5
    have : Fact p.Prime := ⟨hp⟩
    have hv : padicValRat p (5:ℚ)=0 := by
      rw [show (5:ℚ)=(5:ℕ) from rfl, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hp5]
      rfl
    apply even_val_triple (a := -5) (b := 5) hx (by simpa only [sub_eq_add_neg] using sub_ne_zero.mpr hx5)
      (by intro hh; apply hxm5; linarith) (by norm_num) (by norm_num) (by simpa using hv) hv
    have he := equation h
    nlinarith only [he]

lemma supported_five (P : E.Point) : ∃ (d : ℕ) (r : ℚ), d ∣ 10 ∧ r ≠ 0 ∧
    (alphaVal 5 P=d*r^2 ∨ alphaVal 5 P=-(d*r^2)) := by
  cases P with
  | zero => exact ⟨1,1,by norm_num,by norm_num,Or.inl (by norm_num [alphaVal])⟩
  | some x y h =>
    by_cases hx : x=0
    · exact ⟨5,1,by norm_num,by norm_num,Or.inr (by norm_num [alphaVal,adjusted,hx])⟩
    by_cases hx5 : x=5
    · exact ⟨2,5,by norm_num,by norm_num,Or.inl (by norm_num [alphaVal,adjusted,hx5])⟩
    by_cases hxm5 : x= -5
    · exact ⟨10,1,by norm_num,by norm_num,Or.inr (by norm_num [alphaVal,adjusted,hxm5])⟩
    have hx5' : x-5 ≠ 0 := sub_ne_zero.mpr hx5
    simp only [alphaVal_some, adjusted, ite_eq_right hx5']
    apply supported_decomposition hx5' (by norm_num)
    intro p hp hp10
    have : Fact p.Prime := ⟨hp⟩
    have hv (k : ℕ) (hk : k ∣ 10) : padicValRat p (k:ℚ)=0 := by
      rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (fun hh => hp10 (hh.trans hk))]
      rfl
    apply even_val_triple (a := 5) (b := 10) hx5' (by simpa using hx)
      (by intro hh; apply hxm5; linarith) (by norm_num) (by norm_num)
      (hv 5 (by norm_num)) (hv 10 (by norm_num))
    have he := equation h
    nlinarith only [he]

lemma classOf_mul_sq {d r : ℚ} (hd : d ≠ 0) (hr : r ≠ 0) :
    classOf (d*r^2)=classOf d := by
  rw [pow_two, classOf_mul hd (mul_ne_zero hr hr), classOf_square, mul_one]

lemma alpha_zero_classes (P : E.Point) :
    classOf (alphaVal 0 P) = classOf 1 ∨ classOf (alphaVal 0 P) = classOf (-1) ∨
    classOf (alphaVal 0 P) = classOf 5 ∨ classOf (alphaVal 0 P) = classOf (-5) := by
  obtain ⟨d,r,hd,hr,he | he⟩ := supported_zero P
  all_goals rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with rfl | rfl
  · left; rw [he]; exact classOf_mul_sq (by norm_num) hr
  · right; right; left; rw [he]; exact classOf_mul_sq (by norm_num) hr
  · right; left; rw [he, ← neg_mul]; exact classOf_mul_sq (by norm_num) hr
  · right; right; right; rw [he, ← neg_mul]; exact classOf_mul_sq (by norm_num) hr

end SingleFold.Descent

end OAI
