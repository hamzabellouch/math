import OAI.LinearAlgebra.Hadamard.Equivalence

namespace OAI

/-! Fourier kernel identities and symmetric polynomials of row ratios. -/

open scoped BigOperators Matrix

namespace HadamardSix

lemma character_sub (x : Index → ℂ) (hx : ∀ i, ‖x i‖ = 1) (a b : Charge) :
    character x (a - b) = character x a * star (character x b) := by
  rw [sub_eq_add_neg, character_add x (fun k => unit_ne_zero (hx k)), character_neg x hx]

lemma column_kernel_identity {H : Matrix6} (hH : IsComplexHadamard H)
    (A B : Index → ℂ) (i : Index) :
    (∑ j, (∑ k, A k * H i k * star (H j k)) *
      (∑ l, B l * star (H i l) * H j l)) = 6 * ∑ k, A k * B k := by
  have hexpand :
      (∑ j, (∑ k, A k * H i k * star (H j k)) *
        (∑ l, B l * star (H i l) * H j l)) =
      ∑ k, ∑ l, A k * B l * H i k * star (H i l) *
        ∑ j, star (H j k) * H j l := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexpand]
  simp_rw [hH.column_orthogonality]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    A k * B k * H i k * star (H i k) * 6 = 6 * (A k * B k) *
        (H i k * star (H i k)) := by ring
    _ = 6 * (A k * B k) := by rw [unit_mul_star (hH.1 i k), mul_one]

lemma same_matrix_identity {H : Matrix6} (hH : IsComplexHadamard H)
    (a b : Charge) (i : Index) :
    ∑ j, g H (a + differenceCharge 1 i j) * g H (b - differenceCharge 1 i j) =
      g H (a + b) := by
  have hplus (j : Index) :
      g H (a + differenceCharge 1 i j) = (6 : ℂ)⁻¹ *
        ∑ k, character (fun t => H t k) a * H i k * star (H j k) := by
    unfold g
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [character_add _ (fun t => hH.1.entry_ne_zero t k),
      character_difference _ (fun t => hH.1 t k)]
    simp [mul_assoc]
  have hminus (j : Index) :
      g H (b - differenceCharge 1 i j) = (6 : ℂ)⁻¹ *
        ∑ k, character (fun t => H t k) b * star (H i k) * H j k := by
    unfold g
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [character_sub _ (fun t => hH.1 t k),
      character_difference _ (fun t => hH.1 t k)]
    simp only [zpow_one, star_mul, star_star]
    ring
  simp_rw [hplus, hminus]
  have hscale (x y : ℂ) : (6 : ℂ)⁻¹ * x * ((6 : ℂ)⁻¹ * y) =
      (6 : ℂ)⁻¹ ^ 2 * (x * y) := by ring
  simp_rw [hscale]
  rw [← Finset.mul_sum, column_kernel_identity hH]
  unfold g
  simp_rw [character_add _ (fun t => hH.1.entry_ne_zero t _)]
  ring

noncomputable def elementary (v : Index → ℂ) (k : ℕ) : ℂ :=
  (Finset.univ.val.map v).esymm k

lemma elementary_eq_sum (v : Index → ℂ) (k : ℕ) :
    elementary v k = ∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, v i :=
  Finset.esymm_map_val v Finset.univ k

lemma elementary_zero (v : Index → ℂ) : elementary v 0 = 1 := by
  simp [elementary_eq_sum]

lemma elementary_one (v : Index → ℂ) : elementary v 1 = ∑ i, v i := by
  simp [elementary_eq_sum, Finset.powersetCard_one]

lemma elementary_six (v : Index → ℂ) : elementary v 6 = ∏ i, v i := by
  rw [elementary_eq_sum]
  have hcard : (Finset.univ : Finset Index).card = 6 := by decide
  rw [show Finset.univ.powersetCard 6 = ({Finset.univ} : Finset (Finset Index)) by
    simpa only [hcard] using Finset.powersetCard_self (Finset.univ : Finset Index)]
  rw [Finset.sum_singleton]

lemma elementary_two_of_power_sums (v : Index → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) : elementary v 2 = 0 := by
  have ha : (Finset.HasAntidiagonal.antidiagonal 2 : Finset (ℕ × ℕ)) =
      {(0, 2), (1, 1), (2, 0)} := by decide
  have hnpoly := MvPolynomial.mul_esymm_eq_sum Index ℂ 2
  rw [ha] at hnpoly
  norm_num [Finset.sum_filter] at hnpoly
  have hn := congrArg (MvPolynomial.aeval v : MvPolynomial Index ℂ →ₐ[ℂ] ℂ) hnpoly
  simp only [map_mul, map_ofNat, map_neg, map_add, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hn
  simp [MvPolynomial.psum, h1, h2] at hn
  exact hn

lemma elementary_complement (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (k : ℕ) (hk : k ≤ 6) :
    elementary v (6 - k) = elementary v 6 * star (elementary v k) := by
  rw [elementary_eq_sum, elementary_six, elementary_eq_sum, star_sum, Finset.mul_sum]
  refine Finset.sum_bij' (fun s _ => sᶜ) (fun s _ => sᶜ) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rw [Finset.mem_powersetCard_univ] at hs ⊢
    rw [Finset.card_compl, Fintype.card_fin, hs, Nat.sub_sub_self hk]
  · intro s hs
    rw [Finset.mem_powersetCard_univ] at hs ⊢
    rw [Finset.card_compl, Fintype.card_fin, hs]
  · intro s hs
    exact compl_compl s
  · intro s hs
    exact compl_compl s
  · intro s hs
    have hunit : ‖∏ i ∈ sᶜ, v i‖ = 1 := by
      simp [norm_prod, hv]
    rw [← Finset.prod_mul_prod_compl s v, mul_assoc, unit_mul_star hunit, mul_one]

noncomputable def ratioPolynomial (v : Index → ℂ) : Polynomial ℂ :=
  ∏ i, (Polynomial.X - Polynomial.C (v i))

lemma ratioPolynomial_vieta (v : Index → ℂ) :
    ratioPolynomial v = ∑ k ∈ Finset.range 7,
      (-1) ^ k * (Polynomial.C (elementary v k) * Polynomial.X ^ (6 - k)) := by
  have h := Multiset.prod_X_sub_X_eq_sum_esymm (Finset.univ.val.map v)
  simp only [Multiset.card_map, ← Finset.card_def,
    Finset.card_univ, Fintype.card_fin] at h
  simpa only [ratioPolynomial, Finset.prod_eq_multiset_prod, Multiset.map_map,
    Function.comp_apply, elementary] using h

lemma ratioPolynomial_of_power_sums (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    ratioPolynomial v = Polynomial.X ^ 6 -
      Polynomial.C (elementary v 3) * Polynomial.X ^ 3 +
      Polynomial.C (elementary v 6) := by
  have e1 : elementary v 1 = 0 := by rw [elementary_one, h1]
  have e2 := elementary_two_of_power_sums v h1 h2
  have e4 : elementary v 4 = 0 := by
    simpa only [e2, star_zero, mul_zero] using elementary_complement v hv 2 (by decide)
  have e5 : elementary v 5 = 0 := by
    simpa only [e1, star_zero, mul_zero] using elementary_complement v hv 1 (by decide)
  rw [ratioPolynomial_vieta]
  norm_num [Finset.sum_range_succ, elementary_zero, e1, e2, e4, e5, sub_eq_add_neg]

lemma ratioPolynomial_eval (v : Index → ℂ) (i : Index) :
    (ratioPolynomial v).eval (v i) = 0 := by
  classical
  rw [ratioPolynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

lemma ratio_power_six (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) (i : Index) :
    v i ^ 6 - elementary v 3 * v i ^ 3 + elementary v 6 = 0 := by
  have h := ratioPolynomial_eval v i
  rw [ratioPolynomial_of_power_sums v hv h1 h2] at h
  simpa using h

lemma ratio_cubes_two_values (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) (i : Index) :
    v i ^ 3 = v 0 ^ 3 ∨ v i ^ 3 = elementary v 3 - v 0 ^ 3 := by
  have hz : (v i ^ 3 - v 0 ^ 3) * (v i ^ 3 - (elementary v 3 - v 0 ^ 3)) = 0 := by
    linear_combination ratio_power_six v hv h1 h2 i - ratio_power_six v hv h1 h2 0
  simpa only [sub_eq_zero] using mul_eq_zero.mp hz

lemma three_mul_elementary_three (v : Index → ℂ)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) :
    3 * elementary v 3 = ∑ i, v i ^ 3 := by
  have ha : (Finset.HasAntidiagonal.antidiagonal 3 : Finset (ℕ × ℕ)) =
      {(0, 3), (1, 2), (2, 1), (3, 0)} := by decide
  have hnpoly := MvPolynomial.mul_esymm_eq_sum Index ℂ 3
  rw [ha] at hnpoly
  norm_num [Finset.sum_filter] at hnpoly
  have hn := congrArg (MvPolynomial.aeval v : MvPolynomial Index ℂ →ₐ[ℂ] ℂ) hnpoly
  simp only [map_mul, map_ofNat, map_neg, map_add, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hn
  simpa [elementary, MvPolynomial.psum, h1, h2] using hn

lemma fourth_power_sum_zero (v : Index → ℂ) (hv : ∀ i, ‖v i‖ = 1)
    (h1 : ∑ i, v i = 0) (h2 : ∑ i, v i ^ 2 = 0) : ∑ i, v i ^ 4 = 0 := by
  have ha : (Finset.HasAntidiagonal.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by decide
  have he4 : elementary v 4 = 0 := by
    simpa only [elementary_two_of_power_sums v h1 h2, star_zero, mul_zero]
      using elementary_complement v hv 2 (by decide)
  have hnpoly := MvPolynomial.mul_esymm_eq_sum Index ℂ 4
  rw [ha] at hnpoly
  norm_num [Finset.sum_filter] at hnpoly
  have hn := congrArg (MvPolynomial.aeval v : MvPolynomial Index ℂ →ₐ[ℂ] ℂ) hnpoly
  simp only [map_mul, map_ofNat, map_neg, map_add, map_sum,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at hn
  have hn' : 4 * elementary v 4 = -(∑ i, v i ^ 4) := by
    simpa [elementary, MvPolynomial.psum, h1, h2] using hn
  rw [he4] at hn'
  simpa using hn'.symm

end HadamardSix

end OAI
