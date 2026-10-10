import OAI.NumberTheory.ShortEgyptian.LowerBound

namespace OAI

universe uι uG

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem additive_orthogonality {q : ℕ} [NeZero q] (t : ZMod q) :
    (∑ x : ZMod q, ZMod.stdAddChar (t * x)) = if t = 0 then (q : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)

theorem finite_parseval {q : ℕ} [NeZero q] (β : ZMod q → ℂ) :
    ∑ x : ZMod q, ‖∑ y : ZMod q, β y * ZMod.stdAddChar (x * y)‖ ^ 2 =
      (q : ℝ) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    ← AddChar.map_neg_eq_conj]
  have hterm (x y z : ZMod q) :
      β y * ZMod.stdAddChar (x * y) *
        ((starRingEnd ℂ) (β z) * ZMod.stdAddChar (-(x * z))) =
      (β y * (starRingEnd ℂ) (β z)) * ZMod.stdAddChar ((y - z) * x) := by
    rw [show (y - z) * x = x * y + -(x * z) by ring, AddChar.map_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun y _ => Finset.sum_comm))
  simp only [← Finset.mul_sum, additive_orthogonality, sub_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem bilinear_character_sq_bound {q : ℕ} [NeZero q]
    (α β : ZMod q → ℂ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar (x * y)‖ ^ 2 ≤
      (q : ℝ) * (∑ x : ZMod q, ‖α x‖ ^ 2) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  let F (x : ZMod q) := ∑ y : ZMod q, β y * ZMod.stdAddChar (x * y)
  have heq : (∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar (x * y)) =
      ∑ x : ZMod q, α x * F x := by simp [F, Finset.mul_sum, mul_assoc]
  rw [heq]
  have hn : ‖∑ x : ZMod q, α x * F x‖ ≤ ∑ x : ZMod q, ‖α x‖ * ‖F x‖ := by
    simpa only [norm_mul] using norm_sum_le (Finset.univ : Finset (ZMod q)) (fun x => α x * F x)
  have hn0 : 0 ≤ ∑ x : ZMod q, ‖α x‖ * ‖F x‖ := Finset.sum_nonneg (by intros; positivity)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun x => ‖α x‖) (fun x => ‖F x‖)
  have hP : (∑ x : ZMod q, ‖F x‖ ^ 2) = q * ∑ y : ZMod q, ‖β y‖ ^ 2 := finite_parseval β
  rw [hP] at hc
  have hh : ‖∑ x : ZMod q, α x * F x‖ ^ 2 ≤
      (∑ x : ZMod q, ‖α x‖ * ‖F x‖) ^ 2 := sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn
  exact hh.trans (by simpa only [mul_left_comm, mul_assoc] using hc)

theorem bilinear_character_unit_sq_bound {q : ℕ} [NeZero q]
    (c : (ZMod q)ˣ) (α β : ZMod q → ℂ) :
    ‖∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ^ 2 ≤
      (q : ℝ) * (∑ x : ZMod q, ‖α x‖ ^ 2) * ∑ y : ZMod q, ‖β y‖ ^ 2 := by
  let α' (x : ZMod q) := α ((↑c⁻¹ : ZMod q) * x)
  have heq : (∑ x : ZMod q, ∑ y : ZMod q, α x * β y * ZMod.stdAddChar ((c : ZMod q) * x * y)) =
      ∑ x : ZMod q, ∑ y : ZMod q, α' x * β y * ZMod.stdAddChar (x * y) := by
    apply Fintype.sum_equiv (Units.mulLeft c)
    intro x
    simp [α', Units.mulLeft_apply, ← mul_assoc]
  have hmass : (∑ x : ZMod q, ‖α' x‖ ^ 2) = ∑ x : ZMod q, ‖α x‖ ^ 2 := by
    apply Fintype.sum_equiv (Units.mulLeft c⁻¹)
    intro x
    rfl
  rw [heq]
  simpa only [hmass] using bilinear_character_sq_bound α' β

theorem real_probability_energy_bound {ι : Type uι} [Fintype ι]
    (α : ι → ℝ) (A : ℝ) (hpos : ∀ i, 0 ≤ α i) (hsum : ∑ i, α i = 1)
    (hatom : ∀ i, α i ≤ A) : (∑ i, ‖(α i : ℂ)‖ ^ 2) ≤ A := by
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos _)]
  calc
    ∑ i, α i ^ 2 ≤ ∑ i, A * α i := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_le_mul_of_nonneg_right (hatom i) (hpos i)]
    _ = A := by rw [← Finset.mul_sum, hsum, mul_one]

theorem bilinear_probability_bound {q : ℕ} [NeZero q]
    (c : (ZMod q)ˣ) (α β : ZMod q → ℝ) (A B : ℝ)
    (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x)
    (hsα : ∑ x, α x = 1) (hsβ : ∑ x, β x = 1)
    (haα : ∀ x, α x ≤ A) (haβ : ∀ x, β x ≤ B) :
    ‖∑ x : ZMod q, ∑ y : ZMod q,
      (α x : ℂ) * (β y : ℂ) * ZMod.stdAddChar ((c : ZMod q) * x * y)‖ ≤
      Real.sqrt ((q : ℝ) * A * B) := by
  have hA : 0 ≤ A := le_trans (hα 0) (haα 0)
  have hB : 0 ≤ B := le_trans (hβ 0) (haβ 0)
  have hα2 := real_probability_energy_bound α A hα hsα haα
  have hβ2 := real_probability_energy_bound β B hβ hsβ haβ
  have hh := bilinear_character_unit_sq_bound c (fun x => (α x : ℂ)) (fun y => (β y : ℂ))
  have hsα0 : 0 ≤ ∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hsβ0 : 0 ≤ ∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2 := Finset.sum_nonneg (by intros; positivity)
  have hh' : (q : ℝ) * (∑ x : ZMod q, ‖(α x : ℂ)‖ ^ 2) * ∑ y : ZMod q, ‖(β y : ℂ)‖ ^ 2 ≤
      q * A * B := by gcongr
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr (hh.trans hh')

theorem complex_sum_sq_le {ι : Type uι} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hn := norm_sum_le s f
  have hs0 : 0 ≤ ∑ i ∈ s, ‖f i‖ := Finset.sum_nonneg (by intros; positivity)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  exact ((sq_le_sq₀ (norm_nonneg _) hs0).mpr hn).trans hc

theorem complex_sum_norm_sq {ι : Type uι} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ s, (f i * (starRingEnd ℂ) (f j)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
  exact Finset.sum_comm

theorem finite_van_der_corput {G : Type uG} [Fintype G] [AddCommGroup G]
    (H : Finset G) (hH : H.Nonempty) (a : G → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hcorr : ∀ h ∈ H, ∀ k ∈ H, h ≠ k →
      ‖∑ x : G, a (x + h) * (starRingEnd ℂ) (a (x + k))‖ ≤ C) :
    ‖∑ x : G, a x‖ ^ 2 ≤
      (Fintype.card G : ℝ) / H.card * (∑ x : G, ‖a x‖ ^ 2) +
      Fintype.card G * C := by
  classical
  let F (x : G) := ∑ h ∈ H, a (x + h)
  let E : ℝ := ∑ x : G, ‖a x‖ ^ 2
  have hshift (h : G) : (∑ x : G, a (x + h)) = ∑ x : G, a x := by
    exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)
  have hshiftE (h : G) : (∑ x : G, ‖a (x + h)‖ ^ 2) = E := by
    exact Fintype.sum_equiv (Equiv.addRight h) _ _ (fun _ => rfl)
  have hsum : (∑ x : G, F x) = (H.card : ℂ) * ∑ x : G, a x := by
    rw [show (∑ x : G, F x) = ∑ h ∈ H, ∑ x : G, a (x + h) from Finset.sum_comm]
    simp only [hshift, Finset.sum_const, nsmul_eq_mul]
  have hterm (h : G) (hh : h ∈ H) (k : G) (hk : k ∈ H) :
      (∑ x : G, (a (x + h) * (starRingEnd ℂ) (a (x + k))).re) ≤
        (if h = k then E else 0) + C := by
    by_cases heq : h = k
    · subst k
      simp only [ite_true, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [hshiftE]
      linarith
    · rw [ite_eq_right heq, zero_add, ← Complex.re_sum]
      exact (Complex.re_le_norm _).trans (hcorr h hh k hk heq)
  have hE : (∑ x : G, ‖F x‖ ^ 2) ≤ H.card * E + (H.card : ℝ) ^ 2 * C := by
    simp only [F, complex_sum_norm_sq]
    rw [Finset.sum_comm]
    have hex : (∑ h ∈ H, ∑ x : G, ∑ k ∈ H,
        (a (x + h) * (starRingEnd ℂ) (a (x + k))).re) =
        ∑ h ∈ H, ∑ k ∈ H, ∑ x : G,
        (a (x + h) * (starRingEnd ℂ) (a (x + k))).re := by
      apply Finset.sum_congr rfl
      intro h _
      exact Finset.sum_comm
    rw [hex]
    calc
      _ ≤ ∑ h ∈ H, ∑ k ∈ H, ((if h = k then E else 0) + C) := by
        apply Finset.sum_le_sum
        intro h hh
        apply Finset.sum_le_sum
        intro k hk
        exact hterm h hh k hk
      _ = H.card * E + (H.card : ℝ) ^ 2 * C := by
        simp [Finset.sum_add_distrib, Finset.sum_ite_eq, pow_two, mul_assoc]
  have hcs := complex_sum_sq_le (Finset.univ : Finset G) F
  rw [hsum, norm_mul, Complex.norm_natCast, mul_pow, Finset.card_univ] at hcs
  have hcard : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hN : (0 : ℝ) ≤ Fintype.card G := by positivity
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hE hN)
  have heq : (H.card : ℝ) ^ 2 *
      ((Fintype.card G : ℝ) / H.card * E + Fintype.card G * C) =
      Fintype.card G * (H.card * E + (H.card : ℝ) ^ 2 * C) := by
    field_simp
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hcard)).mp
  rw [heq]
  exact hbound

end ShortEgyptian

end OAI
