import Mathlib

namespace OAI

namespace PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section PolynomialShift
variable {σ R : Type*} [CommSemiring R]

noncomputable def shift (c : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (c i))

@[simp] theorem shift_C (c : σ → R) (r : R) : shift c (C r) = C r := by
  simp [shift]

@[simp] theorem shift_X (c : σ → R) (i : σ) : shift c (X i) = X i + C (c i) := by
  simp [shift]

theorem shift_add (c d : σ → R) (p : MvPolynomial σ R) :
    shift c (shift d p) = shift (fun i => c i + d i) p := by
  have h : (shift c).comp (shift d) = shift (fun i => c i + d i) := by
    ext r i <;> simp [add_assoc]
  exact DFunLike.congr_fun h p

@[simp] theorem shift_zero (p : MvPolynomial σ R) : shift (fun _ => 0) p = p := by
  have h : shift (fun _ : σ => (0 : R)) = RingHom.id _ := by
    ext r i <;> simp
  exact DFunLike.congr_fun h p

noncomputable def shiftCoefficient (c : σ → R) (β a : σ →₀ ℕ) : R :=
  (shift c (monomial a 1)).coeff β

theorem coeff_shift (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ) :
    (shift c p).coeff β =
      ∑ a ∈ p.support, p.coeff a * shiftCoefficient c β a := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show monomial a (p.coeff a) = C (p.coeff a) * monomial a 1 by simp [C_mul_monomial]]
  simp [shiftCoefficient, coeff_C_mul]

theorem coeff_shift_over (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) :
    (shift c p).coeff β = ∑ a ∈ S, p.coeff a * shiftCoefficient c β a := by
  classical
  rw [coeff_shift]
  apply Finset.sum_subset hp
  intro a ha hnot
  simp [MvPolynomial.notMem_support_iff.mp hnot]

theorem shift_three (z ε τ : σ → R) (p : MvPolynomial σ R) :
    shift (fun i => z i + ε i + τ i) p = shift τ (shift ε (shift z p)) := by
  simp only [shift_add]
  apply congrArg (fun c => shift c p)
  funext i
  ac_rfl

end PolynomialShift

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

noncomputable def multiIndex (a : σ → ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm a

omit [DecidableEq σ] in
@[simp] theorem multiIndex_apply (a : σ → ℕ) (i : σ) : multiIndex a i = a i := by
  simp [multiIndex]

omit [Fintype σ] [DecidableEq σ] in
theorem shifted_X_pow (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem shifted_product_expansion (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_X_pow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator]
  rw [hidx]

omit [DecidableEq σ] in
theorem shift_monomial_one (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

theorem shiftCoefficient_eq (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial_one, shifted_product_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by ext i; simp [b₀]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]

theorem product_add_expansion (ε τ : σ → R) (n : σ → ℕ) :
    (∏ i, (ε i + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        (∏ i, (n i).choose (d i) : ℕ) *
          (∏ i, ε i ^ (n i - d i)) * ∏ i, τ i ^ (d i : ℕ) := by
  have h (i : σ) : (ε i + τ i) ^ n i =
      ∑ d : Fin (n i + 1), ((n i).choose d : R) * ε i ^ (n i - d) * τ i ^ (d : ℕ) := by
    rw [add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.prod_mul_distrib, Nat.cast_prod]

end FiniteExpansion

section FormalSeriesRow
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

omit [Fintype σ] [DecidableEq σ] in
theorem row_coefficient_identity (c : σ → PowerSeries R)
    (p : MvPolynomial σ (PowerSeries R)) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) (s : ℕ) :
    PowerSeries.coeff s ((shift c p).coeff β) =
      ∑ a ∈ S, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
        PowerSeries.coeff kl.1 (shiftCoefficient c β a) *
          PowerSeries.coeff kl.2 (p.coeff a) := by
  rw [coeff_shift_over c p β S hp]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm, PowerSeries.coeff_mul]

theorem coefficient_error_tail (ε : σ → R) (τ : σ → PowerSeries R)
    (n : σ → ℕ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, (PowerSeries.C (ε i) + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        ((∏ i, (n i).choose (d i) : ℕ) : R) *
          (∏ i, ε i ^ (n i - d i)) *
            PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ)) := by
  rw [product_add_expansion]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [← map_pow, ← map_prod]
  rw [show ((∏ i, (n i).choose (d i) : ℕ) : PowerSeries R) =
      PowerSeries.C (((∏ i, (n i).choose (d i) : ℕ) : R)) by simp]
  rw [← map_mul, PowerSeries.coeff_C_mul]

noncomputable def rowScalar (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) : R :=
  ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : R) *
    (∏ i, ε i ^ (a i - β i - d i)) *
      PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))

omit [DecidableEq σ] in
theorem rowScalar_ne_zero_le (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ)
    (h : rowScalar ε τ β a d k ≠ 0) : β ≤ a := by
  intro i
  by_contra hn
  have hi : a i < β i := by omega
  have hp : (∏ j, (a j).choose (β j) * (a j - β j).choose (d j) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  exact h (by simp [rowScalar, hp])

theorem coeff_shiftCoefficient_error_tail (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (shiftCoefficient (fun i => PowerSeries.C (ε i) + τ i) β a) =
      ∑ d : (∀ i, Fin (a i - β i + 1)), rowScalar ε τ β a d k := by
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib]
  have hcast : (∏ i, ((a i).choose (β i) : PowerSeries R)) =
      PowerSeries.C ((∏ i, (a i).choose (β i) : ℕ) : R) := by simp
  rw [hcast, PowerSeries.coeff_C_mul, coefficient_error_tail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [rowScalar, Finset.prod_mul_distrib, Nat.cast_mul]
  ring

theorem exact_row_identity (ε : σ → R) (τ : σ → PowerSeries R)
    (p : MvPolynomial σ (PowerSeries R)) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) (s : ℕ) :
    PowerSeries.coeff s ((shift (fun i => PowerSeries.C (ε i) + τ i) p).coeff β) =
      ∑ a ∈ S, ∑ d : (∀ i, Fin (a i - β i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar ε τ β a d kl.1 * PowerSeries.coeff kl.2 (p.coeff a) := by
  rw [row_coefficient_identity _ p β S hp s]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [coeff_shiftCoefficient_error_tail, Finset.sum_mul]
  rw [Finset.sum_comm]

end FormalSeriesRow

section FiniteExpansion
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem choose_product_le_four_pow (a β d : ℕ) :
    a.choose β * (a - β).choose d ≤ 4 ^ a := by
  calc
    a.choose β * (a - β).choose d ≤ 2 ^ a * 2 ^ (a - β) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    _ = 4 ^ a := by rw [← mul_pow]; norm_num

omit [DecidableEq σ] in
theorem multi_choose_product_le_four_pow (a β d : σ → ℕ) :
    (∏ i, (a i).choose (β i) * (a i - β i).choose (d i)) ≤
      4 ^ (∑ i, a i) := by
  calc
    _ ≤ ∏ i, 4 ^ a i := Finset.prod_le_prod (fun i hi => choose_product_le_four_pow _ _ _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem card_bounded_indices_le (a : σ → ℕ) (H : ℕ) (ha : ∀ i, a i ≤ H) :
    Fintype.card (∀ i, Fin (a i + 1)) ≤ (H + 1) ^ Fintype.card σ := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _i : σ, (H + 1) := Finset.prod_le_prod (fun i hi => Nat.add_le_add_right (ha i) 1)
    _ = _ := by simp

abbrev RowChoices (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s : ℕ) :=
  Σ a : S, (∀ i, Fin (a.1 i - β i + 1)) × Fin (s + 1)

theorem card_rowChoices_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H) :
    Fintype.card (RowChoices S β s) ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ ∑ _a : S, (H + 1) ^ Fintype.card σ * (s + 1) := by
      apply Finset.sum_le_sum
      intro a ha'
      apply Nat.mul_le_mul_right
      exact card_bounded_indices_le _ H (fun i => (Nat.sub_le _ _).trans (ha a.1 a.2 i))
    _ = _ := by simp [Nat.mul_assoc]

theorem card_rowChoices_box_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H)
    (hS : S.card ≤ (H + 1) ^ Fintype.card σ) :
    Fintype.card (RowChoices S β s) ≤ (H + 1) ^ (2 * Fintype.card σ) * (s + 1) := by
  calc
    _ ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := card_rowChoices_le S β s H ha
    _ ≤ (H + 1) ^ Fintype.card σ * (H + 1) ^ Fintype.card σ * (s + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS)
    _ = _ := by rw [← pow_add]; congr 2; omega


omit [DecidableEq σ] in
theorem norm_rowScalar_le (ε : σ → ℂ) (τ : σ → PowerSeries ℂ)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (B : ℝ)
    (hτ : ‖PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))‖ ≤ B) :
    ‖rowScalar ε τ β a d k‖ ≤
      (4 : ℝ) ^ (∑ i, a i) * (∏ i, ‖ε i‖ ^ (a i - β i - d i)) * B := by
  have hbin : ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (∑ i, a i) := by
    exact_mod_cast multi_choose_product_le_four_pow (fun i => a i) (fun i => β i) (fun i => (d i : ℕ))
  simp only [rowScalar, norm_mul, norm_prod, norm_pow, Complex.norm_natCast]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hbin (by positivity)) hτ
    (norm_nonneg _) (by positivity)

end FiniteExpansion

variable {R : Type*} [CommRing R]

noncomputable def tail (T : ℕ) (f : PowerSeries R) : PowerSeries R :=
  (PowerSeries.trunc T f : PowerSeries R) - f

@[simp] theorem coeff_tail_of_lt (T k : ℕ) (f : PowerSeries R) (hk : k < T) :
    PowerSeries.coeff k (tail T f) = 0 := by
  simp [tail, PowerSeries.coeff_trunc, hk]

theorem order_tail (T : ℕ) (f : PowerSeries R) :
    (T : ℕ∞) ≤ (tail T f).order := by
  apply PowerSeries.nat_le_order
  exact fun k hk => coeff_tail_of_lt T k f hk

theorem order_tail_prod {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) :
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, tail (T i) (f i) ^ d i).order := by
  calc
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) = ∑ i ∈ s, d i • (T i : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, d i • (tail (T i) (f i)).order := by
      exact Finset.sum_le_sum (fun i hi => nsmul_le_nsmul_right (order_tail _ _) _)
    _ ≤ ∑ i ∈ s, (tail (T i) (f i) ^ d i).order := by
      exact Finset.sum_le_sum (fun i hi => PowerSeries.le_order_pow _ _)
    _ ≤ (∏ i ∈ s, tail (T i) (f i) ^ d i).order := PowerSeries.le_order_prod _ _

theorem tail_budget_nat {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, d i * T i ≤ k := by
  exact_mod_cast (order_tail_prod s T d f).trans (PowerSeries.order_le k hk)

theorem tail_weight_budget {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ) (w : ι → ℝ) (v F : ℝ)
    (hv : 0 ≤ v) (hF : 0 < F)
    (hT : ∀ i ∈ s, F * w i ≤ v * T i)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, (d i : ℝ) * w i ≤ v * k / F := by
  apply (le_div_iff₀ hF).2
  calc
    (∑ i ∈ s, (d i : ℝ) * w i) * F =
        ∑ i ∈ s, (d i : ℝ) * (F * w i) := by rw [Finset.sum_mul]; congr 1; ext i; ring
    _ ≤ ∑ i ∈ s, (d i : ℝ) * (v * T i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hT i hi) (Nat.cast_nonneg _))
    _ = v * (∑ i ∈ s, (d i * T i : ℕ) : ℕ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ v * k := mul_le_mul_of_nonneg_left (by exact_mod_cast tail_budget_nat s T d f k hk) hv

end PiExponent.RowTranslation

end OAI
