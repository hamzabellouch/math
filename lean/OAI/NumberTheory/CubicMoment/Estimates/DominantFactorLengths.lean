import OAI.NumberTheory.CubicMoment.Estimates.AllShortMoments

namespace OAI

/-! The remaining lengths and values after selecting a dominant short factor. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Removing a factor of length at least `Y^(1-δ)` leaves total length at
most `C*Y^δ`, including the fixed dyadic discrepancy `C`. -/
theorem remaining_length_bound (X : ι → ℝ) (i : ι) {Y C δ : ℝ}
    (hY : 0 < Y) (hX : ∀ k, 0 ≤ X k) (_hC : 0 ≤ C)
    (htotal : (∏ k, X k) ≤ C*Y) (hlong : Y^(1-δ) ≤ X i) :
    (∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y^δ := by
  have hrem : 0 ≤ ∏ k ∈ Finset.univ.erase i, X k :=
    Finset.prod_nonneg (fun k _ => hX k)
  have hprod : Y^(1-δ)*(∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y := by
    calc
      _ ≤ X i*(∏ k ∈ Finset.univ.erase i, X k) := mul_le_mul_of_nonneg_right hlong hrem
      _ = ∏ k, X k := Finset.mul_prod_erase Finset.univ X (Finset.mem_univ i)
      _ ≤ C*Y := htotal
  have hid : Y^(1-δ)*(C*Y^δ) = C*Y := by
    rw [mul_left_comm,← Real.rpow_add hY]
    simp only [sub_add_cancel,Real.rpow_one]
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hY (1-δ))).mp (hprod.trans_eq hid.symm)

private lemma single_le_remaining (X : ι → ℝ) {i k : ι}
    (hX : ∀ j, 1 ≤ X j) (hki : k ≠ i) :
    X k ≤ ∏ j ∈ Finset.univ.erase i, X j := by
  calc
    X k = ∏ j ∈ ({k} : Finset ι), X j := by simp
    _ ≤ ∏ j ∈ Finset.univ.erase i, X j :=
      Finset.prod_le_prod_of_subset_of_one_le₀ (by simpa using hki)
        (fun j _ => (zero_le_one.trans (hX j))) (fun j _ _ => hX j)

/-- An explicit scale condition makes a dominant factor unique. -/
theorem dominant_factor_unique (X : ι → ℝ) {Y C δ : ℝ}
    (hY : 0 < Y) (hX : ∀ k, 1 ≤ X k) (hC : 0 ≤ C)
    (htotal : (∏ k, X k) ≤ C*Y) (hscale : C < Y^(1-2*δ))
    {i k : ι} (hi : Y^(1-δ) ≤ X i) (hk : Y^(1-δ) ≤ X k) : i = k := by
  by_contra hne
  have hrem := remaining_length_bound X i hY (fun j => zero_le_one.trans (hX j)) hC htotal hi
  have hother := single_le_remaining X hX (Ne.symm hne)
  have hlt : C*Y^δ < Y^(1-δ) := by
    calc
      _ < Y^(1-2*δ)*Y^δ := mul_lt_mul_of_pos_right hscale (Real.rpow_pos_of_pos hY δ)
      _ = Y^(1-δ) := by rw [← Real.rpow_add hY]; congr 1; ring
  exact (not_lt_of_ge (hk.trans (hother.trans hrem))) hlt

omit [DecidableEq ι] in
/-- For `δ<1/2` the uniqueness condition holds beyond one common threshold. -/
theorem dominant_factor_eventually_unique {C δ : ℝ} (hC : 0 ≤ C) (hδ : δ < 1/2) :
    ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ (Y : ℝ), Y₀ ≤ Y → ∀ (X : ι → ℝ),
      (∀ k, 1 ≤ X k) → (∏ k, X k) ≤ C*Y →
      ∀ i k, Y^(1-δ) ≤ X i → Y^(1-δ) ≤ X k → i = k := by
  classical
  have hp : 0 < 1-2*δ := by linarith
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((tendsto_rpow_atTop hp).eventually_gt_atTop C)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY X hX htotal i k hi hk
  have hY₁ : 1 ≤ Y := (le_max_left _ _).trans hY
  exact dominant_factor_unique X (zero_lt_one.trans_le hY₁) hX hC htotal
    (hT Y ((le_max_right _ _).trans hY)) hi hk

private lemma remaining_value_product_bound (X : ι → ℝ) (f : ι → ℂ) (i : ι)
    {Y C K δ η : ℝ} (hY : 1 ≤ Y) (hC : 0 < C) (hK : 1 ≤ K)
    (hX : ∀ k, 1 ≤ X k) (hη : 0 ≤ η)
    (hrem : (∏ k ∈ Finset.univ.erase i, X k) ≤ C*Y^δ)
    (hf : ∀ k ∈ Finset.univ.erase i, ‖f k‖ ≤ K*(X k)^(1+η)) :
    ‖∏ k ∈ Finset.univ.erase i, f k‖ ≤
      K^(Fintype.card ι)*C^(1+η)*Y^(δ*(1+η)) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hXpos : ∀ k, 0 ≤ X k := fun k => zero_le_one.trans (hX k)
  have hp : K^((Finset.univ.erase i).card) ≤ K^(Fintype.card ι) :=
    pow_le_pow_right₀ hK (by simpa only [Finset.card_univ] using
      (Finset.card_le_card (Finset.erase_subset i Finset.univ)))
  calc
    _ = ∏ k ∈ Finset.univ.erase i, ‖f k‖ := norm_prod _ _
    _ ≤ ∏ k ∈ Finset.univ.erase i, (K*(X k)^(1+η)) :=
      Finset.prod_le_prod₀ (fun _ _ => _root_.norm_nonneg _) hf
    _ = K^((Finset.univ.erase i).card)*(∏ k ∈ Finset.univ.erase i, X k)^(1+η) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,
        Real.finsetProd_rpow _ _ (fun k _ => hXpos k)]
    _ ≤ K^(Fintype.card ι)*(C*Y^δ)^(1+η) :=
      mul_le_mul hp (Real.rpow_le_rpow (Finset.prod_nonneg (fun k _ => hXpos k)) hrem
        (by linarith)) (Real.rpow_nonneg (Finset.prod_nonneg (fun k _ => hXpos k)) _)
        (pow_nonneg (zero_le_one.trans hK) _)
    _ = _ := by
      rw [Real.mul_rpow hC.le (Real.rpow_nonneg hYp.le δ),← Real.rpow_mul hYp.le]
      ring

/-- Uniformly bounded twists of the actual short arithmetic polynomials
have a small remaining product after one dominant factor is removed. -/
theorem short_remaining_polynomial_bound {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ) (i : ι),
      1 ≤ Y → (∀ k, 1 ≤ X k) → (∀ k, ShortArithmeticFactor F (A k)) →
      (∀ k, ∀ n ∈ primaryElementBall (X k), ‖u k n‖ ≤ 1) →
      (∏ k, X k) ≤ C*Y → Y^(1-δ) ≤ X i →
      ‖∏ k ∈ Finset.univ.erase i, primaryIdealPolynomial (X k) (A k) (u k)‖ ≤
        M*Y^(δ+ε) := by
  let η : ℝ := ε/(δ+1)
  have hη : 0 < η := div_pos hε (by linarith)
  have hηδ : δ*(1+η) ≤ δ+ε := by
    have he : η*(δ+1) = ε := div_mul_cancel₀ _ (by linarith)
    nlinarith
  obtain ⟨K₀,hK₀,hbound⟩ := shortFactorPolynomial_norm_small_power hη
  let K : ℝ := max 1 K₀
  have hK : 1 ≤ K := le_max_left _ _
  have hKM : K₀ ≤ K := le_max_right _ _
  refine ⟨K^(Fintype.card ι)*C^(1+η),mul_pos
    (pow_pos (zero_lt_one.trans_le hK) _) (Real.rpow_pos_of_pos hC _),?_⟩
  intro F Y X A u i hY hX hA hu htotal hlong
  have hr := remaining_length_bound X i (zero_lt_one.trans_le hY)
    (fun k => zero_le_one.trans (hX k)) hC.le htotal hlong
  have hf (k : ι) (_hk : k ∈ Finset.univ.erase i) :
      ‖primaryIdealPolynomial (X k) (A k) (u k)‖ ≤ K*(X k)^(1+η) :=
    (hbound F (X k) (A k) (hA k) (hX k) (u k) (hu k)).trans
      (mul_le_mul_of_nonneg_right hKM (Real.rpow_nonneg (zero_le_one.trans (hX k)) _))
  exact (remaining_value_product_bound X
    (fun k => primaryIdealPolynomial (X k) (A k) (u k)) i hY hC hK hX hη.le hr hf).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY hηδ)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) (Real.rpow_nonneg hC.le _)))

/-- The remaining actual cubic factor values contribute at most a constant
multiple of `Y^(δ+ε)`, uniformly over all short-factor data. -/
theorem remaining_cubic_values_bound {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (p : Eisenstein), 1 ≤ Y → primary p →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      ‖∏ k ∈ Finset.univ.erase i, F.cubicValue j k p‖ ≤ M*Y^(δ+ε) := by
  obtain ⟨M,hM,hbound⟩ := short_remaining_polynomial_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i p hY hp htotal hlong
  apply hbound (F.cutoff j) Y (F.length j) (F.coefficient j)
    (fun k n => F.twist j k n*cubicSymbol p n) i hY (F.length_ge_one j) (F.factor_spec j)
    ?_ htotal hlong
  intro k n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j k n hn) (norm_cubicSymbol_le_one hp n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The same remaining-product bound for the actual mixed cubic values. -/
theorem remaining_mixed_values_bound {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (p : Eisenstein × Eisenstein), 1 ≤ Y → primary p.1 → primary p.2 →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      ‖∏ k ∈ Finset.univ.erase i, F.mixedValue j k p‖ ≤ M*Y^(δ+ε) := by
  obtain ⟨M,hM,hbound⟩ := short_remaining_polynomial_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i p hY hp hq htotal hlong
  apply hbound (F.cutoff j) Y (F.length j) (F.coefficient j)
    (fun k n => F.twist j k n*mixedCubic p.1 p.2 n) i hY (F.length_ge_one j) (F.factor_spec j)
    ?_ htotal hlong
  intro k n hn
  rw [norm_mul]
  exact (mul_le_mul (F.twist_bound j k n hn) (norm_mixedCubic_le_one hp hq n)
    (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- A common bound for the other factors reduces the full product moment
to the moment of a single fixed dominant factor. -/
theorem moment_le_dominant_factor {κ : Type*} (S : Finset κ)
    (f : ι → κ → ℂ) (i : ι) (B : ℝ)
    (hB : ∀ r ∈ S, ‖∏ k ∈ Finset.univ.erase i, f k r‖ ≤ B) :
    (∑ r ∈ S, ‖∏ k, f k r‖^2) ≤ B^2*(∑ r ∈ S, ‖f i r‖^2) := by
  calc
    _ ≤ ∑ r ∈ S, B^2*‖f i r‖^2 := by
      apply Finset.sum_le_sum
      intro r hr
      rw [← Finset.mul_prod_erase Finset.univ (fun k => f k r) (Finset.mem_univ i),
        norm_mul,mul_pow]
      have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _ ) (hB r hr) 2
      nlinarith [sq_nonneg ‖f i r‖]
    _ = _ := (Finset.mul_sum S (fun r => ‖f i r‖^2) (B^2)).symm

/-- Moment reduction for a fixed dominant cubic factor; all the remaining
short arithmetic coefficients and independent twists have been bounded. -/
theorem dominant_cubic_moment_reduction {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (S : Finset Eisenstein), 1 ≤ Y → (∀ p ∈ S, primary p) →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      (∑ p ∈ S, ‖∏ k, F.cubicValue j k p‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ S, ‖F.cubicValue j i p‖^2) := by
  obtain ⟨M,hM,hbound⟩ := remaining_cubic_values_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i S hY hS htotal hlong
  exact moment_le_dominant_factor S (F.cubicValue j) i (M*Y^(δ+ε))
    (fun p hp => hbound F j Y i p hY (hS p hp) htotal hlong)

/-- The corresponding moment reduction for a dominant mixed cubic factor. -/
theorem dominant_mixed_moment_reduction {C δ ε : ℝ}
    (hC : 0 < C) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ (F : ShortFactorFamily ι) (j : ℕ) (Y : ℝ) (i : ι)
      (S : Finset (Eisenstein × Eisenstein)), 1 ≤ Y →
      (∀ p ∈ S, primary p.1 ∧ primary p.2) →
      (∏ k, F.length j k) ≤ C*Y → Y^(1-δ) ≤ F.length j i →
      (∑ p ∈ S, ‖∏ k, F.mixedValue j k p‖^2) ≤
        (M*Y^(δ+ε))^2*(∑ p ∈ S, ‖F.mixedValue j i p‖^2) := by
  obtain ⟨M,hM,hbound⟩ := remaining_mixed_values_bound (ι := ι) hC hδ hε
  refine ⟨M,hM,?_⟩
  intro F j Y i S hY hS htotal hlong
  exact moment_le_dominant_factor S (F.mixedValue j) i (M*Y^(δ+ε))
    (fun p hp => hbound F j Y i p hY (hS p hp).1 (hS p hp).2 htotal hlong)

end CubicFirstMoment

end

end OAI
