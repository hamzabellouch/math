import Mathlib

namespace OAI

/-! Quantitative local isolation estimates for critical points. -/

noncomputable section

namespace AmbientMultiplicity.CriticalEstimates
open Filter Topology

def hX (X T : ℂ) : ℂ := T*(2*X-3*T^2)
def hT (X T : ℂ) : ℂ := X^2-9*T^2*X+10*T^4

def delta (X T : ℂ) : ℂ := 2*X-3*T^2

lemma gradient_T_bound (X T : ℂ) (hsmall : ‖T‖ ≤ 1) :
    ‖T‖^4 ≤ 4*‖hX X T‖+4*‖hT X T‖ := by
  have hD : 0 ≤ ‖delta X T‖ := norm_nonneg _
  have ht : 0 ≤ ‖T‖ := norm_nonneg _
  have hx : ‖hX X T‖ = ‖T‖*‖delta X T‖ := by simp [hX, delta]
  by_cases hc : ‖delta X T‖ ≤ ‖T‖^2/4
  · have hid : (5 : ℂ)*T^4 = (delta X T)^2 - 12*T^2*delta X T - 4*hT X T := by
      dsimp [delta,hT]
      ring
    have he : 5*‖T‖^4 ≤ ‖delta X T‖^2+12*‖T‖^2*‖delta X T‖+4*‖hT X T‖ := by
      calc
        5*‖T‖^4 = ‖(5 : ℂ)*T^4‖ := by simp [norm_pow]
        _ = ‖(delta X T)^2 - 12*T^2*delta X T - 4*hT X T‖ := congrArg norm hid
        _ ≤ ‖(delta X T)^2 - 12*T^2*delta X T‖ + ‖4*hT X T‖ := norm_sub_le _ _
        _ ≤ (‖(delta X T)^2‖ + ‖12*T^2*delta X T‖) + ‖4*hT X T‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
        _ = _ := by simp [norm_pow]
    have hd2 : ‖delta X T‖^2 ≤ ‖T‖^4/16 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ ‖T‖^2/4+‖delta X T‖ by positivity)]
    have hd3 : 12*‖T‖^2*‖delta X T‖ ≤ 3*‖T‖^4 := by
      nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg ‖T‖)]
    nlinarith [norm_nonneg (hX X T), norm_nonneg (hT X T)]
  · have hc' : ‖T‖^2/4 ≤ ‖delta X T‖ := le_of_lt (not_le.mp hc)
    have ht4 : ‖T‖^4 ≤ ‖T‖^3 := by
      nlinarith [mul_nonneg (pow_nonneg ht 3) (sub_nonneg.mpr hsmall)]
    rw [hx]
    nlinarith [mul_le_mul_of_nonneg_left hc' ht, norm_nonneg (hT X T)]

lemma gradient_X_bound (X T : ℂ) (hsmall : ‖X‖ ≤ 1) :
    ‖X‖^4 ≤ 2*‖hT X T‖+101*‖T‖^4 := by
  have hid : X^2 = hT X T + 9*T^2*X - 10*T^4 := by dsimp [hT]; ring
  have he : ‖X‖^2 ≤ ‖hT X T‖+9*‖T‖^2*‖X‖+10*‖T‖^4 := by
    calc
      ‖X‖^2 = ‖X^2‖ := (norm_pow _ _).symm
      _ = ‖hT X T+9*T^2*X-10*T^4‖ := congrArg norm hid
      _ ≤ ‖hT X T+9*T^2*X‖+‖10*T^4‖ := norm_sub_le _ _
      _ ≤ (‖hT X T‖+‖9*T^2*X‖)+‖10*T^4‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp [norm_pow]
  have hx0 := norm_nonneg X
  have hx2 : ‖X‖^2 ≤ 1 := pow_le_one₀ hx0 hsmall
  have hx4 : ‖X‖^4 ≤ ‖X‖^2 := by nlinarith [mul_nonneg (sq_nonneg ‖X‖) (sub_nonneg.mpr hx2)]
  nlinarith [sq_nonneg (‖X‖-9*‖T‖^2)]

 
theorem gradient_bound (X T : ℂ) (hXsmall : ‖X‖ ≤ 1) (hTsmall : ‖T‖ ≤ 1) :
    (max ‖X‖ ‖T‖)^4 ≤ 512*(‖hX X T‖+‖hT X T‖) := by
  have h1 := gradient_T_bound X T hTsmall
  have h2 := gradient_X_bound X T hXsmall
  rcases le_total ‖X‖ ‖T‖ with h | h
  · rw [max_eq_right h]
    nlinarith [norm_nonneg (hX X T), norm_nonneg (hT X T)]
  · rw [max_eq_left h]
    nlinarith [norm_nonneg (hX X T), norm_nonneg (hT X T)]


 

lemma vertical_euler_relation (a b : ℕ) (ξ u Y Z R Ru χ : ℂ)
    (hc : Y * Z = R) (hχ : χ ≠ 0)
    (hu : ξ * (Y ^ a + Z ^ b) = -χ * Ru)
    (hY : ξ * a * u * Y ^ (a - 1) = χ * Z)
    (hZ : ξ * b * u * Z ^ (b - 1) = χ * Y)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a : ℂ) * b * u * Ru + (a + b : ℂ) * R = 0 := by
  have ea : Y ^ (a - 1) * Y = Y ^ a := by rw [← pow_succ]; congr 1; omega
  have eb : Z ^ (b - 1) * Z = Z ^ b := by rw [← pow_succ]; congr 1; omega
  have hYa : ξ * a * u * Y ^ a = χ * R := by
    calc
      _ = (ξ * a * u * Y ^ (a - 1)) * Y := by rw [← ea]; ring
      _ = χ * R := by rw [hY]; rw [← hc]; ring
  have hZb : ξ * b * u * Z ^ b = χ * R := by
    calc
      _ = (ξ * b * u * Z ^ (b - 1)) * Z := by rw [← eb]; ring
      _ = χ * R := by rw [hZ, ← hc]; ring
  apply (mul_eq_zero.mp (show χ * ((a : ℂ) * b * u * Ru + (a + b : ℂ) * R) = 0 from ?_)).resolve_left hχ
  linear_combination (a : ℂ) * b * u * hu - b * hYa - a * hZb

 

lemma vertical_multiplier_product (a b : ℕ) (ξ u Y Z χ : ℂ)
    (hY0 : Y ≠ 0) (hZ0 : Z ≠ 0)
    (hY : ξ * a * u * Y ^ (a - 1) = χ * Z)
    (hZ : ξ * b * u * Z ^ (b - 1) = χ * Y)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    χ ^ 2 = ξ ^ 2 * (a : ℂ) * b * u ^ 2 * Y ^ (a - 2) * Z ^ (b - 2) := by
  have ea : Y ^ (a - 1) = Y ^ (a - 2) * Y := by rw [← pow_succ]; congr 1; omega
  have eb : Z ^ (b - 1) = Z ^ (b - 2) * Z := by rw [← pow_succ]; congr 1; omega
  apply mul_right_cancel₀ (mul_ne_zero hY0 hZ0)
  calc
    χ ^ 2 * (Y * Z) = (χ * Z) * (χ * Y) := by ring
    _ = (ξ * a * u * Y ^ (a - 1)) * (ξ * b * u * Z ^ (b - 1)) := by rw [hY, hZ]
    _ = _ := by rw [ea, eb]; ring


lemma vertical_multiplier_bound (a b : ℕ) (ξ u Y Z χ : ℂ)
    (hY0 : Y ≠ 0) (hZ0 : Z ≠ 0)
    (hY : ξ * a * u * Y ^ (a - 1) = χ * Z)
    (hZ : ξ * b * u * Z ^ (b - 1) = χ * Y)
    (ha : 11 ≤ a) (hb : 11 ≤ b)
    (hu1 : ‖u‖ ≤ 1) (hY1 : ‖Y‖ ≤ 1) (hZ1 : ‖Z‖ ≤ 1) :
    ‖χ‖ ^ 2 ≤ ‖ξ‖ ^ 2 * (a : ℝ) * b * ‖Y * Z‖ ^ 9 := by
  have he := vertical_multiplier_product a b ξ u Y Z χ hY0 hZ0 hY hZ (by omega) (by omega)
  have hY9 := pow_le_pow_of_le_one (norm_nonneg Y) hY1 (show 9 ≤ a - 2 by omega)
  have hZ9 := pow_le_pow_of_le_one (norm_nonneg Z) hZ1 (show 9 ≤ b - 2 by omega)
  calc
    ‖χ‖ ^ 2 = ‖ξ‖ ^ 2 * (a : ℝ) * b * ‖u‖ ^ 2 * ‖Y‖ ^ (a - 2) * ‖Z‖ ^ (b - 2) := by
      simpa only [norm_pow, norm_mul, norm_natCast] using congrArg norm he
    _ ≤ ‖ξ‖ ^ 2 * (a : ℝ) * b * 1 * ‖Y‖ ^ 9 * ‖Z‖ ^ 9 := by
      gcongr
      exact pow_le_one₀ (norm_nonneg u) hu1
    _ = _ := by rw [norm_mul, mul_pow]; ring

def quartic (A : Fin 4 → ℂ) (u : ℂ) : ℂ := u ^ 4 + ∑ j : Fin 4, A j * u ^ (j : ℕ)
def quarticD (A : Fin 4 → ℂ) (u : ℂ) : ℂ :=
  4 * u ^ 3 + ∑ j : Fin 4, (j : ℂ) * A j * u ^ ((j : ℕ) - 1)

lemma quartic_euler_expansion (a b : ℕ) (A : Fin 4 → ℂ) (u : ℂ)
    (he : (a : ℂ) * b * u * quarticD A u + (a + b : ℂ) * quartic A u = 0) :
    ((4 * a * b + a + b : ℕ) : ℂ) * u ^ 4 =
      -(∑ j : Fin 4, ((a * b * (j : ℕ) + a + b : ℕ) : ℂ) * A j * u ^ (j : ℕ)) := by
  simp only [quarticD, quartic, Fin.sum_univ_four] at he ⊢
  norm_num at he ⊢
  linear_combination he

 
lemma quartic_euler_bound (a b : ℕ) (A : Fin 4 → ℂ) (u : ℂ) (M : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hM : 0 ≤ M)
    (hA : ∀ j, ‖A j‖ ≤ M) (hu : ‖u‖ ≤ 1)
    (he : (a : ℂ) * b * u * quarticD A u + (a + b : ℂ) * quartic A u = 0) :
    ‖u‖ ^ 4 ≤ 4 * M ∧ ‖quartic A u‖ ≤ 8 * M := by
  let D : ℕ := 4 * a * b + a + b
  have hD : 0 < (D : ℝ) := by dsimp [D]; positivity
  have hj (j : Fin 4) : a * b * (j : ℕ) + a + b ≤ D := by
    dsimp [D]
    have hj4 : (j : ℕ) ≤ 4 := by omega
    have hjm := Nat.mul_le_mul_left (a * b) hj4
    nlinarith only [hjm]
  have hp (j : Fin 4) : ‖u‖ ^ (j : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
  have hc : (D : ℝ) * ‖u‖ ^ 4 ≤ (D : ℝ) * (4 * M) := by
    calc
      (D : ℝ) * ‖u‖ ^ 4 = ‖((D : ℕ) : ℂ) * u ^ 4‖ := by simp
      _ = ‖∑ j : Fin 4, ((a * b * (j : ℕ) + a + b : ℕ) : ℂ) * A j * u ^ (j : ℕ)‖ := by
        rw [show D = 4 * a * b + a + b from rfl, quartic_euler_expansion a b A u he, norm_neg]
      _ ≤ ∑ j : Fin 4, ‖((a * b * (j : ℕ) + a + b : ℕ) : ℂ) * A j * u ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin 4, (D : ℝ) * M := by
        apply Finset.sum_le_sum
        intro j _
        simp only [norm_mul, norm_pow, norm_natCast]
        calc
          _ ≤ (D : ℝ) * M * 1 := by
            gcongr
            exact_mod_cast hj j
            exact hA j
            exact hp j
          _ = _ := mul_one _
      _ = (D : ℝ) * (4 * M) := by simp; ring
  have hu4 : ‖u‖ ^ 4 ≤ 4 * M := (mul_le_mul_iff_right₀ hD).mp hc
  refine ⟨hu4, ?_⟩
  calc
    ‖quartic A u‖ ≤ ‖u‖ ^ 4 + ∑ j : Fin 4, ‖A j * u ^ (j : ℕ)‖ := by
      calc
        _ ≤ ‖u ^ 4‖ + ‖∑ j : Fin 4, A j * u ^ (j : ℕ)‖ := norm_add_le _ _
        _ ≤ _ := by simp only [norm_pow]; exact add_le_add (le_refl _) (norm_sum_le Finset.univ (fun j : Fin 4 => A j * u ^ (j : ℕ)))
    _ ≤ 4 * M + ∑ _j : Fin 4, M := by
      apply add_le_add hu4
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, norm_pow]
      calc
        _ ≤ M * 1 := mul_le_mul (hA j) (hp j) (by positivity) hM
        _ = M := mul_one M
    _ = 8 * M := by simp; ring


def isolationConstant (a b : ℕ) (ξ : ℂ) (B C : ℝ) : ℝ :=
  (512 * B) ^ 2 * (‖ξ‖ ^ 2 * (a : ℝ) * b) * (8 * C) ^ 9

 

theorem critical_nonzero_base_vertical_zero
    (a b : ℕ) (ξ X T u Y Z χ RX RT : ℂ) (A : Fin 4 → ℂ) (B C : ℝ)
    (ha : 11 ≤ a) (hb : 11 ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hX1 : ‖X‖ ≤ 1) (hT1 : ‖T‖ ≤ 1)
    (hu1 : ‖u‖ ≤ 1) (hY1 : ‖Y‖ ≤ 1) (hZ1 : ‖Z‖ ≤ 1)
    (hbase : 0 < max ‖X‖ ‖T‖)
    (hcoeff : ∀ j, ‖A j‖ ≤ C * max ‖X‖ ‖T‖)
    (hRbound : ‖RX‖ + ‖RT‖ ≤ B)
    (hsmall : isolationConstant a b ξ B C * max ‖X‖ ‖T‖ < 1)
    (hc : Y * Z = quartic A u)
    (hX : hX X T = -χ * RX) (hT : hT X T = -χ * RT)
    (hu : ξ * (Y ^ a + Z ^ b) = -χ * quarticD A u)
    (hY : ξ * a * u * Y ^ (a - 1) = χ * Z)
    (hZ : ξ * b * u * Z ^ (b - 1) = χ * Y) :
    Y = 0 ∧ Z = 0 := by
  let K := max ‖X‖ ‖T‖
  have hK : 0 < K := hbase
  have hg : K ^ 4 ≤ 512 * B * ‖χ‖ := by
    calc
      K ^ 4 ≤ 512 * (‖CriticalEstimates.hX X T‖ + ‖CriticalEstimates.hT X T‖) := gradient_bound X T hX1 hT1
      _ = 512 * ‖χ‖ * (‖RX‖ + ‖RT‖) := by rw [hX, hT]; simp only [norm_mul, norm_neg]; ring
      _ ≤ 512 * ‖χ‖ * B := mul_le_mul_of_nonneg_left hRbound (by positivity)
      _ = _ := by ring
  have hχ : χ ≠ 0 := by
    intro he
    rw [he, norm_zero, mul_zero] at hg
    exact (not_le_of_gt (pow_pos hK 4)) hg
  by_cases hY0 : Y = 0
  · refine ⟨hY0, ?_⟩
    have hZ' : χ * Z = 0 := by simpa [hY0, show a - 1 ≠ 0 by omega] using hY.symm
    exact (mul_eq_zero.mp hZ').resolve_left hχ
  by_cases hZ0 : Z = 0
  · have hY' : χ * Y = 0 := by simpa [hZ0, show b - 1 ≠ 0 by omega] using hZ.symm
    exact ⟨(mul_eq_zero.mp hY').resolve_left hχ, hZ0⟩
  have he := vertical_euler_relation a b ξ u Y Z (quartic A u) (quarticD A u) χ
    hc hχ hu hY hZ (by omega) (by omega)
  have hq := (quartic_euler_bound a b A u (C * K) (by omega) (by omega)
    (mul_nonneg hC hK.le) hcoeff hu1 he).2
  have hm := vertical_multiplier_bound a b ξ u Y Z χ hY0 hZ0 hY hZ ha hb hu1 hY1 hZ1
  have hm' : ‖χ‖ ^ 2 ≤ (‖ξ‖ ^ 2 * (a : ℝ) * b) * (8 * C) ^ 9 * K ^ 9 := by
    calc
      ‖χ‖ ^ 2 ≤ (‖ξ‖ ^ 2 * (a : ℝ) * b) * ‖Y * Z‖ ^ 9 := hm
      _ ≤ (‖ξ‖ ^ 2 * (a : ℝ) * b) * (8 * (C * K)) ^ 9 := by rw [hc]; gcongr
      _ = _ := by ring
  have hh : K ^ 8 ≤ isolationConstant a b ξ B C * K ^ 9 := by
    calc
      K ^ 8 = (K ^ 4) ^ 2 := by ring
      _ ≤ (512 * B * ‖χ‖) ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
      _ = (512 * B) ^ 2 * ‖χ‖ ^ 2 := mul_pow _ _ _
      _ ≤ (512 * B) ^ 2 * ((‖ξ‖ ^ 2 * (a : ℝ) * b) * (8 * C) ^ 9 * K ^ 9) :=
        mul_le_mul_of_nonneg_left hm' (pow_nonneg (mul_nonneg (by norm_num) hB) 2)
      _ = _ := by dsimp [isolationConstant]; ring
  have hlt : isolationConstant a b ξ B C * K ^ 9 < K ^ 8 := by
    calc
      _ = K ^ 8 * (isolationConstant a b ξ B C * K) := by ring
      _ < K ^ 8 * 1 := mul_lt_mul_of_pos_left hsmall (pow_pos hK 8)
      _ = _ := mul_one _
  exact False.elim ((not_lt_of_ge hh) hlt)
 

theorem critical_zero_base (a b : ℕ) (ξ u Y Z χ : ℂ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hξ : ξ ≠ 0)
    (hc : Y * Z = u ^ 4)
    (hu : ξ * (Y ^ a + Z ^ b) = -χ * (4 * u ^ 3))
    (hY : ξ * a * u * Y ^ (a - 1) = χ * Z)
    (hZ : ξ * b * u * Z ^ (b - 1) = χ * Y) :
    u = 0 ∧ Y = 0 ∧ Z = 0 := by
  have hu0 : u = 0 := by
    by_contra hnu
    have hYZ : Y * Z ≠ 0 := by rw [hc]; exact pow_ne_zero 4 hnu
    have hYn : Y ≠ 0 := (mul_ne_zero_iff.mp hYZ).1
    have hχ : χ ≠ 0 := by
      intro he
      have hn : ξ * (a : ℂ) * u * Y ^ (a - 1) ≠ 0 := by
        apply mul_ne_zero
        · exact mul_ne_zero (mul_ne_zero hξ (by exact_mod_cast (show a ≠ 0 by omega))) hnu
        · exact pow_ne_zero _ hYn
      exact hn (by simpa [he] using hY)
    have he := vertical_euler_relation a b ξ u Y Z (u ^ 4) (4 * u ^ 3) χ
      hc hχ hu hY hZ (by omega) (by omega)
    have he' : ((4 * a * b + a + b : ℕ) : ℂ) * u ^ 4 = 0 := by
      push_cast
      linear_combination he
    have hn : ((4 * a * b + a + b : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show 4 * a * b + a + b ≠ 0 by omega)
    exact (mul_ne_zero hn (pow_ne_zero 4 hnu)) he'
  refine ⟨hu0, ?_⟩
  have hsum : Y ^ a + Z ^ b = 0 := by
    apply (mul_eq_zero.mp (show ξ * (Y ^ a + Z ^ b) = 0 by simpa [hu0] using hu)).resolve_left hξ
  have hprod : Y * Z = 0 := by simpa [hu0] using hc
  rcases mul_eq_zero.mp hprod with hY0 | hZ0
  · refine ⟨hY0, ?_⟩
    have hzpow : Z ^ b = 0 := by simpa [hY0, show a ≠ 0 by omega] using hsum
    exact (eq_zero_of_pow_eq_zero hzpow)
  · refine ⟨?_, hZ0⟩
    have hypow : Y ^ a = 0 := by simpa [hZ0, show b ≠ 0 by omega] using hsum
    exact (eq_zero_of_pow_eq_zero hypow)
end AmbientMultiplicity.CriticalEstimates

namespace AmbientMultiplicity.LocalIsolation
open Filter Topology Asymptotics
abbrev V (n : ℕ) := Fin n → ℂ
abbrev proj {n : ℕ} (i : Fin n) : V n →L[ℂ] ℂ := ContinuousLinearMap.proj i

theorem norm_two (p : V 2) : ‖p‖ = max ‖p 0‖ ‖p 1‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (norm_le_pi_norm p 0) (norm_le_pi_norm p 1)

 

theorem coefficient_bound {A : V 2 → V 4} (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ p in 𝓝 (0 : V 2),
      ∀ j, ‖A p j‖ ≤ C * max ‖p 0‖ ‖p 1‖ := by
  obtain ⟨C, hC, hb⟩ := hA.differentiableAt.isBigO_sub.exists_nonneg
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb.bound] with p hp
  intro j
  have hp' : ‖A p‖ ≤ C * ‖p‖ := by simpa [hA0] using hp
  rw [norm_two] at hp'
  exact (norm_le_pi_norm (A p) j).trans hp'

 
theorem derivative_bound {R : V 3 → ℂ} (hR : AnalyticAt ℂ R 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ z in 𝓝 (0 : V 3),
      ‖fderiv ℂ R z (Pi.single 0 1)‖ + ‖fderiv ℂ R z (Pi.single 1 1)‖ ≤ B := by
  have hd : ContinuousAt (fderiv ℂ R) (0 : V 3) :=
    (hR.contDiffAt (n := 1)).continuousAt_fderiv (by norm_num)
  have hn := hd.norm
  have he : ∀ᶠ z in 𝓝 (0 : V 3), ‖fderiv ℂ R z‖ < ‖fderiv ℂ R 0‖ + 1 :=
    hn.eventually (eventually_lt_nhds (by linarith))
  refine ⟨2 * (‖fderiv ℂ R 0‖ + 1), by positivity, ?_⟩
  filter_upwards [he] with z hz
  have h (i : Fin 3) : ‖fderiv ℂ R z (Pi.single i 1)‖ ≤ ‖fderiv ℂ R z‖ := by
    have hh := (fderiv ℂ R z).le_opNorm (Pi.single i 1)
    simpa [Pi.norm_single] using hh
  linarith [h 0, h 1]
end AmbientMultiplicity.LocalIsolation
namespace AmbientMultiplicity.CriticalEstimates
open Filter Topology
abbrev V (n : ℕ) := Fin n → ℂ

def base2 : V 3 →L[ℂ] V 2 := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.castSucc

def preparedRoot (A : V 2 → V 4) (z : V 3) : ℂ := quartic (A (base2 z)) (z 2)

lemma quartic_deriv (A : V 4) (u : ℂ) : HasDerivAt (quartic A) (quarticD A u) u := by
  have hs : HasDerivAt (fun u => ∑ j : Fin 4, A j * u ^ (j : ℕ))
      (∑ j : Fin 4, A j * ((j : ℂ) * u ^ ((j : ℕ) - 1))) u := by
    exact HasDerivAt.fun_sum fun j _ => by
      simpa only [Pi.pow_apply, id_eq, mul_one] using ((hasDerivAt_id u).pow (j : ℕ)).const_mul (A j)
  convert! ((hasDerivAt_id u).pow 4).add hs using 1
  simp only [quarticD, id_eq, mul_one, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma preparedRoot_analytic {A : V 2 → V 4} (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℂ (preparedRoot A) 0 := by
  unfold preparedRoot quartic
  apply AnalyticAt.add
  · exact ((ContinuousLinearMap.proj (2 : Fin 3) : V 3 →L[ℂ] ℂ).analyticAt 0).pow 4
  · apply Finset.analyticAt_fun_sum
    intro j _
    apply AnalyticAt.mul
    · have hp : AnalyticAt ℂ (fun p => A p j) (base2 0) := by
        simpa only [map_zero, Function.comp_def, ContinuousLinearMap.proj_apply] using
          ((ContinuousLinearMap.proj j).analyticAt (A 0)).comp hA
      exact hp.comp (base2.analyticAt 0)
    · exact ((ContinuousLinearMap.proj (2 : Fin 3) : V 3 →L[ℂ] ℂ).analyticAt 0).pow (j : ℕ)

lemma preparedRoot_u_deriv {A : V 2 → V 4} {z : V 3}
    (hR : DifferentiableAt ℂ (preparedRoot A) z) :
    fderiv ℂ (preparedRoot A) z (Pi.single 2 1) = quarticD (A (base2 z)) (z 2) := by
  let ins : ℂ → V 3 := fun t => ![z 0, z 1, t]
  have hins : HasDerivAt ins (Pi.single 2 1) (z 2) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [ins] using hasDerivAt_const (z 2) (z 0)
    · simpa [ins] using hasDerivAt_const (z 2) (z 1)
    · convert! hasDerivAt_id (z 2) using 1
  have heq : ins (z 2) = z := by ext i; fin_cases i <;> rfl
  have hr : HasDerivAt (fun t => preparedRoot A (ins t))
      (fderiv ℂ (preparedRoot A) z (Pi.single 2 1)) (z 2) := by
    have hR' : HasFDerivAt (preparedRoot A) (fderiv ℂ (preparedRoot A) z) (ins (z 2)) := by
      simpa only [heq] using hR.hasFDerivAt
    exact hR'.comp_hasDerivAt (z 2) hins
  have hi (t : ℂ) : base2 (ins t) = base2 z := by ext i; fin_cases i <;> rfl
  have hr' : HasDerivAt (quartic (A (base2 z)))
      (fderiv ℂ (preparedRoot A) z (Pi.single 2 1)) (z 2) := by
    have hf : (fun t => preparedRoot A (ins t)) = quartic (A (base2 z)) := by
      funext t
      simp only [preparedRoot, hi]
      rfl
    rw [hf] at hr
    exact hr
  exact hr'.unique (quartic_deriv _ _)

def base5 : V 5 →L[ℂ] V 3 :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 4]

def ConstrainedCritical (A : V 2 → V 4) (a b : ℕ) (ξ : ℂ) (z : V 5) : Prop :=
  z 2 * z 3 = preparedRoot A (base5 z) ∧ ∃ χ : ℂ,
    hX (z 0) (z 1) = -χ * fderiv ℂ (preparedRoot A) (base5 z) (Pi.single 0 1) ∧
    hT (z 0) (z 1) = -χ * fderiv ℂ (preparedRoot A) (base5 z) (Pi.single 1 1) ∧
    ξ * (z 2 ^ a + z 3 ^ b) = -χ * fderiv ℂ (preparedRoot A) (base5 z) (Pi.single 2 1) ∧
    ξ * a * z 4 * z 2 ^ (a - 1) = χ * z 3 ∧
    ξ * b * z 4 * z 3 ^ (b - 1) = χ * z 2

 
theorem critical_vertical_zero {A : V 2 → V 4}
    (hA : AnalyticAt ℂ A 0) (hA0 : A 0 = 0)
    (a b : ℕ) (ha : 11 ≤ a) (hb : 11 ≤ b) (ξ : ℂ) (hξ : ξ ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : V 5), ConstrainedCritical A a b ξ z → z 2 = 0 ∧ z 3 = 0 := by
  obtain ⟨C, hC, hc⟩ := LocalIsolation.coefficient_bound hA hA0
  have hR := preparedRoot_analytic hA
  obtain ⟨B, hB, hd⟩ := LocalIsolation.derivative_bound hR
  have hb5 : Tendsto base5 (𝓝 (0 : V 5)) (𝓝 0) := by simpa using base5.continuous.tendsto 0
  have hp5 : Tendsto (fun z : V 5 => base2 (base5 z)) (𝓝 0) (𝓝 0) := by
    have hb2 : Tendsto base2 (𝓝 (0 : V 3)) (𝓝 0) := by
      simpa using base2.continuous.tendsto 0
    exact hb2.comp hb5
  have hbound : ∀ᶠ z : V 5 in 𝓝 0, ‖z‖ ≤ 1 := by
    have hc : ContinuousAt (fun z : V 5 => ‖z‖) 0 := continuous_norm.continuousAt
    exact hc.eventually (eventually_le_nhds (by simp))
  have hsmall : ∀ᶠ z : V 5 in 𝓝 0,
      isolationConstant a b ξ B C * max ‖z 0‖ ‖z 1‖ < 1 := by
    have hc : ContinuousAt (fun z : V 5 => isolationConstant a b ξ B C * max ‖z 0‖ ‖z 1‖) 0 := by
      fun_prop
    exact hc.eventually (eventually_lt_nhds (by simp))
  filter_upwards [hp5.eventually hc, hb5.eventually hd, hbound, hsmall,
    hb5.eventually hR.eventually_analyticAt] with z hcoeff hder hbnd hsm hRz
  rintro ⟨he, χ, hx, ht, hu, hy, hz⟩
  have hdU := preparedRoot_u_deriv hRz.differentiableAt
  rw [hdU] at hu
  have hnorm (i : Fin 5) : ‖z i‖ ≤ 1 := (norm_le_pi_norm z i).trans hbnd
  by_cases hk : 0 < max ‖z 0‖ ‖z 1‖
  · exact critical_nonzero_base_vertical_zero a b ξ (z 0) (z 1) (z 4) (z 2) (z 3) χ
      _ _ (A (base2 (base5 z))) B C ha hb hB hC (hnorm 0) (hnorm 1)
      (hnorm 4) (hnorm 2) (hnorm 3) hk hcoeff hder hsm he hx ht hu hy hz
  · have hxp : z 0 = 0 := norm_le_zero_iff.mp ((le_max_left _ _).trans (le_of_not_gt hk))
    have htp : z 1 = 0 := norm_le_zero_iff.mp ((le_max_right _ _).trans (le_of_not_gt hk))
    have hp0 : base2 (base5 z) = 0 := by
      ext i; fin_cases i
      · simpa [base2, base5] using hxp
      · simpa [base2, base5] using htp
    have hA' : A (base2 (base5 z)) = 0 := by rw [hp0, hA0]
    have he' : z 2 * z 3 = z 4 ^ 4 := by
      change z 2 * z 3 = quartic (A (base2 (base5 z))) (z 4) at he
      simpa only [hA', quartic, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using he
    have hu' : ξ * (z 2 ^ a + z 3 ^ b) = -χ * (4 * z 4 ^ 3) := by
      change ξ * (z 2 ^ a + z 3 ^ b) = -χ * quarticD (A (base2 (base5 z))) (z 4) at hu
      simpa only [hA', quarticD, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero] using hu
    exact (critical_zero_base a b ξ (z 4) (z 2) (z 3) χ (by omega) (by omega) hξ he' hu' hy hz).2
end AmbientMultiplicity.CriticalEstimates

end

end OAI
