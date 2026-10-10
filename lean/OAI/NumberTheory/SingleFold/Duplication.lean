import OAI.NumberTheory.SingleFold.Rank

namespace OAI

namespace SingleFold.DuplicationBound

lemma gcd_numerator_divides (a b : ℤ) (h : IsCoprime a b) :
    gcd ((a^2+25*b^2)^2) (4*a*b*(a^2-25*b^2)) ∣ (6250000:ℤ) := by
  let N := (a^2+25*b^2)^2
  have ht : IsCoprime (a^2+25*b^2) b := by
    have hh := (h.pow_left (m:=2)).add_mul_right_left (25*b)
    simpa only [pow_two,mul_assoc] using hh
  have hs : IsCoprime (a^2-25*b^2) b := by
    have hh := (h.pow_left (m:=2)).add_mul_right_left (-25*b)
    simpa only [pow_two,mul_assoc,neg_mul,sub_eq_add_neg] using hh
  have h4 : gcd N 4 ∣ (4:ℤ) := gcd_dvd_right _ _
  have ha : gcd N a ∣ (625:ℤ) := by
    have hcop : IsCoprime (gcd N a) (b^4) :=
      (h.of_isCoprime_of_dvd_left (gcd_dvd_right N a)).pow_right
    apply hcop.dvd_of_dvd_mul_right
    have hh := dvd_sub (gcd_dvd_left N a)
      (dvd_mul_of_dvd_left (gcd_dvd_right N a) (a^3+50*a*b^2))
    convert hh using 1; dsimp [N]; ring
  have hb : gcd N b ∣ (1:ℤ) :=
    ((ht.pow_left (m:=2)).isUnit_of_dvd' (gcd_dvd_left N b) (gcd_dvd_right N b)).dvd
  have hc : gcd N (a^2-25*b^2) ∣ (2500:ℤ) := by
    have hcop : IsCoprime (gcd N (a^2-25*b^2)) (b^4) :=
      (hs.of_isCoprime_of_dvd_left (gcd_dvd_right N _)).pow_right
    apply hcop.dvd_of_dvd_mul_right
    have hh := dvd_sub (gcd_dvd_left N (a^2-25*b^2))
      (dvd_mul_of_dvd_left (gcd_dvd_right N (a^2-25*b^2)) (a^2+75*b^2))
    convert hh using 1; dsimp [N]; ring
  have hh := gcd_mul_dvd_mul_gcd N (4*a*b) (a^2-25*b^2)
  have h₁ := gcd_mul_dvd_mul_gcd N (4*a) b
  have h₂ := gcd_mul_dvd_mul_gcd N 4 a
  exact hh.trans ((mul_dvd_mul
    (h₁.trans (mul_dvd_mul (h₂.trans (mul_dvd_mul h4 ha)) hb)) hc) |>.trans (by norm_num))

lemma common_divisor_bound (a b c : ℤ) (h : IsCoprime a b)
    (hN : c ∣ (a^2+25*b^2)^2) (hD : c ∣ 4*a*b*(a^2-25*b^2)) : c ∣ (6250000:ℤ) :=
  (dvd_gcd hN hD).trans (gcd_numerator_divides a b h)

def height (x : ℚ) : ℕ := max x.num.natAbs x.den

def dupX (x : ℚ) : ℚ := (x^2+25)^2/(4*x*(x^2-25))

lemma dupX_fraction (x : ℚ) : dupX x =
    (((x.num:ℤ)^2+25*(x.den:ℤ)^2)^2 : ℤ) / (4*x.num*x.den*(x.num^2-25*(x.den:ℤ)^2) : ℤ) := by
  have hb : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  conv_lhs => rw [←x.num_div_den]
  unfold dupX
  push_cast
  field_simp

lemma height_dup_lower (x : ℚ) (hx : x ≠ 0) (hs : x^2-25 ≠ 0) :
    height x ^ 4 ≤ 6250000 * height (dupX x) := by
  let a := x.num
  let b : ℤ := x.den
  let N := (a^2+25*b^2)^2
  let D := 4*a*b*(a^2-25*b^2)
  have hb : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have ha : a ≠ 0 := Rat.num_ne_zero.mpr hx
  have hsn : a^2-25*b^2 ≠ 0 := by
    intro hh
    apply hs
    rw [←x.num_div_den]
    dsimp [a,b] at hh
    have hh' : (x.num:ℚ)^2-25*(x.den:ℚ)^2=0 := by exact_mod_cast hh
    field_simp
    nlinarith only [hh']
  have hD : D ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha)
    (by dsimp [b]; exact_mod_cast x.den_ne_zero)) hsn
  have hf : dupX x = Rat.divInt N D := by
    rw [Rat.divInt_eq_div]
    exact dupX_fraction x
  obtain ⟨c,hNc,hDc⟩ := Rat.num_den_mk hD hf
  have hc : c ∣ (6250000:ℤ) := common_divisor_bound a b c x.isCoprime_num_den
    ⟨_,hNc⟩ ⟨_,hDc⟩
  have hc' : c.natAbs ≤ 6250000 := Nat.le_of_dvd (by norm_num) (Int.natAbs_dvd_natAbs.mpr hc)
  have hN : N.natAbs ≤ 6250000 * height (dupX x) := by
    rw [hNc,Int.natAbs_mul]
    exact Nat.mul_le_mul hc' (le_max_left _ _)
  apply le_trans _ hN
  have hN' : (N.natAbs:ℤ)=N := Int.natAbs_of_nonneg (sq_nonneg _)
  have ha' : (a.natAbs:ℤ)^2=a^2 := by rw [Int.natCast_natAbs,sq_abs]
  apply Int.ofNat_le.mp
  rw [hN']
  push_cast
  unfold height
  rcases le_total x.num.natAbs x.den with hl|hl
  · rw [max_eq_right hl]
    change (b^4:ℤ) ≤ (a^2+25*b^2)^2
    nlinarith [sq_nonneg (a^2),sq_nonneg (b^2),mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  · rw [max_eq_left hl]
    change (a.natAbs:ℤ)^4 ≤ (a^2+25*b^2)^2
    rw [show (a.natAbs:ℤ)^4=((a.natAbs:ℤ)^2)^2 by ring,ha']
    nlinarith [sq_nonneg (b^2),mul_nonneg (sq_nonneg a) (sq_nonneg b)]

lemma denominator_square {x y : ℚ} (he : y^2=x^3-25*x) : IsSquare x.den := by
  let a := x.num
  let b : ℤ := x.den
  have hb : 0 < b := by dsimp [b]; exact_mod_cast x.den_pos
  have hbq : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hcop : IsCoprime (a^3-25*a*b^2) (b^3) := by
    apply IsCoprime.pow_right
    have hh := (x.isCoprime_num_den.pow_left (m:=3)).add_mul_right_left (-25*a*b)
    have hn : a^3-25*a*b^2=x.num^3+(-25*a*b)*(x.den:ℤ) := by dsimp [a,b]; ring
    rw [hn]
    exact hh
  have hf : y^2=((a^3-25*a*b^2:ℤ):ℚ)/(b^3:ℤ) := by
    rw [he]
    conv_lhs => rw [←x.num_div_den]
    dsimp [a,b]
    push_cast
    field_simp
  have hd := Rat.den_div_eq_of_coprime (pow_pos hb 3) (Int.isCoprime_iff_nat_coprime.mp hcop)
  rw [←hf,Rat.den_pow] at hd
  dsimp [b] at hd
  have hd' : (y.den:ℚ)^2=(x.den:ℚ)^3 := by exact_mod_cast hd
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(y.den:ℚ)/x.den,?_⟩
  field_simp
  nlinarith only [hd']

lemma bounded_points (i : Fin 19) (j : Fin 20) (k : Fin 13) :
    let x : ℚ := (20*(i.val:ℤ)+(j.val:ℤ)-184) / ((k.val+1:ℕ):ℚ)^2
    IsSquare (x^3-25*x) → x=0 ∨ x=5 ∨ x= -5 ∨ x= -4 ∨ x=45 ∨ x=25/4 ∨ x= -5/9 := by
  fin_cases k <;> fin_cases i <;> revert j <;> decide +kernel

lemma small_points {x y : ℚ} (he : y^2=x^3-25*x) (hH : height x < 185) :
    x=0 ∨ x=5 ∨ x= -5 ∨ x= -4 ∨ x=45 ∨ x=25/4 ∨ x= -5/9 := by
  obtain ⟨k,hk⟩ := denominator_square he
  have hnum : x.num.natAbs < 185 := lt_of_le_of_lt (le_max_left _ _) hH
  have hden : x.den < 185 := lt_of_le_of_lt (le_max_right _ _) hH
  have hkpos : 0 < k := by have := x.den_pos; rw [hk] at this; nlinarith
  have hklt : k < 14 := by rw [hk] at hden; nlinarith
  let a := (x.num+184).toNat
  have ha : (a:ℤ)=x.num+184 := Int.toNat_of_nonneg (by
    have hh' : -(184:ℤ) ≤ x.num := by
      have : (x.num.natAbs:ℤ) ≤ 184 := by exact_mod_cast (show x.num.natAbs ≤ 184 by omega)
      rw [Int.natCast_natAbs] at this
      exact (abs_le.mp this).1
    omega)
  have halt : a < 369 := by
    have hh' : x.num ≤ 184 := by
      have : (x.num.natAbs:ℤ) ≤ 184 := by exact_mod_cast (show x.num.natAbs ≤ 184 by omega)
      rw [Int.natCast_natAbs] at this
      exact (abs_le.mp this).2
    omega
  have harr : 20*(a/20)+a%20=a := by omega
  have hv : (20*(a/20:ℕ)+(a%20:ℕ)-184:ℚ) / ((k-1+1:ℕ):ℚ)^2 = x := by
    rw [show k-1+1=k by omega]
    have hh : (20*(a/20:ℕ)+(a%20:ℕ)-184:ℚ) = (x.num:ℚ) := by
      have haQ : (a:ℚ)=(x.num:ℚ)+184 := by exact_mod_cast ha
      have hrQ : 20*(a/20:ℕ)+(a%20:ℕ)=(a:ℚ) := by exact_mod_cast harr
      linarith
    calc
      _=(x.num:ℚ)/x.den := by rw [hh,hk]; push_cast; ring
      _=x := x.num_div_den
  have h := bounded_points ⟨a/20,by omega⟩ ⟨a%20,by omega⟩ ⟨k-1,by omega⟩
  dsimp only at h
  simp only [Int.cast_natCast] at h
  rw [hv] at h
  exact h ⟨y,by nlinarith only [he]⟩

lemma height_dup_strict {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    height x < height (dupX x) := by
  have hx : x ≠ 0 := by intro h; rw [h] at he; simp at he; exact hy he
  have hs : x^2-25 ≠ 0 := by
    intro h
    have hh : y^2=0 := by linear_combination he+x*h
    exact hy (sq_eq_zero_iff.mp hh)
  by_cases hH : height x < 185
  · rcases small_points he hH with h|h|h|h|h|h|h
    · exact False.elim (hx h)
    · subst x; norm_num at hs
    · subst x; norm_num at hs
    · subst x; decide +kernel
    · subst x; decide +kernel
    · subst x; decide +kernel
    · subst x; decide +kernel
  · have hH' : 185 ≤ height x := by omega
    have hc : 6250000 < height x ^ 3 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hH' 3)
    have hhp : 0 < height x := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right hc hhp
    have hmul' : 6250000*height x < height x^4 := by simpa [pow_succ] using hmul
    have hl := height_dup_lower x hx hs
    nlinarith only [hmul',hl]

lemma height_dup_gt_five {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    5 < height (dupX x) := by
  by_cases hH : 5 ≤ height x
  · exact lt_of_le_of_lt hH (height_dup_strict he hy)
  · rcases small_points he (by omega) with h|h|h|h|h|h|h
    all_goals subst x
    · norm_num at he; exact False.elim (hy he)
    · norm_num at he; exact False.elim (hy he)
    · norm_num at he; exact False.elim (hy he)
    · decide +kernel
    · norm_num [height] at hH
    · norm_num [height] at hH
    · norm_num [height] at hH

lemma height_y_zero {x y : ℚ} (he : y^2=x^3-25*x) (hy : y = 0) : height x ≤ 5 := by
  have h : x*(x-5)*(x+5)=0 := by rw [hy] at he; linear_combination -he
  rcases mul_eq_zero.mp h with h|h
  · rcases mul_eq_zero.mp h with h|h
    · subst x; decide
    · have : x=5 := by linarith
      subst x; decide
  · have : x= -5 := by linarith
    subst x; decide

end SingleFold.DuplicationBound

end OAI
