import Mathlib
import OAI.Probability.SKGap.Terminal.Spin

namespace OAI

section
open scoped BigOperators
namespace SKGapCutoff

theorem exp_apply_hasSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (f : E) :
    HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f))
      (NormedSpace.exp A f) := by
  simpa only [NormedSpace.expSeries_apply_eq, ContinuousLinearMap.apply_apply,
    smul_apply] using
    (ContinuousLinearMap.apply ℝ E f).hasSum
      (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) A)

theorem exp_apply_of_apply_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E)
    (h : A f = 0) : NormedSpace.exp A f = f := by
  have hp (k : ℕ) : (A ^ (k + 1)) f = 0 := by
    induction k with
    | zero => simpa using h
    | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_zero]
  have hs : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ • ((A ^ k) f)) f := by
    convert hasSum_ite_eq 0 f using 1
    funext k
    cases k with
    | zero => simp
    | succ k => simp [hp]
  exact (exp_apply_hasSum A f).unique hs

@[simp] theorem semigroup_const {n : ℕ} (J : Interaction n) (t a : ℝ) :
    semigroup J t (fun _ => a) = fun _ => a := by
  apply exp_apply_of_apply_eq_zero
  funext x
  change t * generator J (fun _ => a) x = 0
  simp

theorem exp_smul_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : ℝ) :
    NormedSpace.exp (a • (1 : E →L[ℝ] E)) = Real.exp a • (1 : E →L[ℝ] E) := by
  simpa only [Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] using
    (NormedSpace.algebraMap_exp_comm (𝔸 := E →L[ℝ] E) a).symm

theorem semigroup_uniformization {n : ℕ} (hn : 0 < n) (J : Interaction n) (t : ℝ) :
    semigroup J t = Real.exp (-(n : ℝ) * t) •
      NormedSpace.exp (((n : ℝ) * t) • attemptLM J) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have heq : t • generatorCLM J =
      (-(n : ℝ) * t) • (1 : Observables n →L[ℝ] Observables n) +
        ((n : ℝ) * t) • attemptLM J := by
    unfold attemptLM
    simp only [smul_add, smul_smul]
    have hc : ((n : ℝ) * t) * (n : ℝ)⁻¹ = t := by field_simp
    rw [hc]
    module
  let : NormedAlgebra ℚ (Observables n →L[ℝ] Observables n) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  unfold semigroup
  rw [heq, NormedSpace.exp_add_of_commute
    (((Commute.one_left (attemptLM J)).smul_left _).smul_right _),
    exp_smul_identity, smul_mul_assoc, one_mul]

theorem semigroup_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (f : Observables n) (hf : ∀ x, 0 ≤ f x) (x : Spin n) :
    0 ≤ semigroup J t f x := by
  by_cases hn : n = 0
  · subst n
    have hL : generatorCLM J = 0 := by
      ext f x
      simp [generatorCLM, generatorLM, generator]
    simp only [semigroup, hL, smul_zero, NormedSpace.exp_zero,
      one_apply_eq_self]
    exact hf x
  · rw [semigroup_uniformization (Nat.pos_of_ne_zero hn)]
    simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
    apply mul_nonneg (le_of_lt (Real.exp_pos _))
    have hs := Pi.hasSum.mp (exp_apply_hasSum (((n : ℝ) * t) • attemptLM J) f) x
    apply HasSum.nonneg _ hs
    intro k
    simp only [smul_pow, smul_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (mul_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) ht) _)
        (attempt_pow_nonneg J k f hf x))

theorem continuousKernel_nonneg {n : ℕ} (J : Interaction n) (t : ℝ) (ht : 0 ≤ t)
    (x y : Spin n) : 0 ≤ continuousKernel J t x y := by
  exact semigroup_nonneg J t ht _ (fun _ => by split_ifs <;> norm_num) x

theorem continuousKernel_sum {n : ℕ} (J : Interaction n) (t : ℝ) (x : Spin n) :
    ∑ y, continuousKernel J t x y = 1 := by
  have eq_one : (∑ y : Spin n, fun z => if z = y then (1 : ℝ) else 0) =
      fun _ : Spin n => (1 : ℝ) := by
    funext z
    simp
  unfold continuousKernel
  rw [← Finset.sum_apply, ← map_sum, eq_one, semigroup_const]

@[simp] theorem spin_sq {n : ℕ} (x : Spin n) (i : Fin n) : spin x i ^ 2 = 1 := by
  unfold spin
  cases x i <;> norm_num

@[simp] theorem spin_mul_self {n : ℕ} (x : Spin n) (i : Fin n) :
    spin x i * spin x i = 1 := by simpa only [pow_two] using spin_sq x i

@[simp] theorem field_zero {n : ℕ} (x : Spin n) (i : Fin n) :
    field (0 : Interaction n) x i = 0 := by simp [field]

@[simp] theorem mean_zero {n : ℕ} (x : Spin n) (i : Fin n) :
    mean (0 : Interaction n) x i = 0 := by simp [mean]

@[simp] theorem energy_zero {n : ℕ} (x : Spin n) :
    energy (0 : Interaction n) x = 0 := by simp [energy]

@[simp] theorem card_spin (n : ℕ) : Fintype.card (Spin n) = 2 ^ n := by
  simp [Spin]

@[simp] theorem partition_zero (n : ℕ) : partition (0 : Interaction n) = (2 : ℝ) ^ n := by
  simp [partition]

@[simp] theorem gibbs_zero {n : ℕ} (x : Spin n) :
    gibbs (0 : Interaction n) x = ((2 : ℝ) ^ n)⁻¹ := by simp [gibbs]

noncomputable def character {n : ℕ} (s : Finset (Fin n)) (x : Spin n) : ℝ :=
  ∏ i ∈ s, spin x i

@[simp] theorem character_empty {n : ℕ} (x : Spin n) : character ∅ x = 1 := by
  simp [character]

@[simp] theorem character_sq {n : ℕ} (s : Finset (Fin n)) (x : Spin n) :
    character s x ^ 2 = 1 := by simp [character, ← Finset.prod_pow]

lemma character_erase {n : ℕ} (s : Finset (Fin n)) (x : Spin n) (i : Fin n)
    (hi : i ∈ s) : spin x i * character (s.erase i) x = character s x := by
  exact Finset.mul_prod_erase s (fun j => spin x j) hi

lemma spin_replace_of_ne {n : ℕ} (x : Spin n) {i j : Fin n} (h : j ≠ i) (b : Bool) :
    spin (replace x i b) j = spin x j := by
  simp [spin, replace, Function.update_of_ne h]

lemma character_replace_of_not_mem {n : ℕ} (s : Finset (Fin n)) (x : Spin n)
    (i : Fin n) (hi : i ∉ s) (b : Bool) : character s (replace x i b) = character s x := by
  apply Finset.prod_congr rfl
  intro j hj
  exact spin_replace_of_ne x (ne_of_mem_of_not_mem hj hi) b

lemma character_replace_of_mem {n : ℕ} (s : Finset (Fin n)) (x : Spin n)
    (i : Fin n) (hi : i ∈ s) (b : Bool) :
    character s (replace x i b) = (if b then 1 else -1) * character (s.erase i) x := by
  rw [← character_erase s (replace x i b) i hi,
    character_replace_of_not_mem _ x i (Finset.notMem_erase i s)]
  simp [spin]

lemma halfDiff_character {n : ℕ} (s : Finset (Fin n)) (x : Spin n) (i : Fin n) :
    halfDiff i (character s) x = if i ∈ s then character (s.erase i) x else 0 := by
  by_cases hi : i ∈ s
  · simp only [halfDiff, character_replace_of_mem s x i hi, Bool.false_eq_true, ↓reduceIte, hi]
    ring
  · simp [halfDiff, character_replace_of_not_mem s x i hi, hi]

lemma spin_mul_halfDiff_character {n : ℕ} (s : Finset (Fin n)) (x : Spin n) (i : Fin n) :
    spin x i * halfDiff i (character s) x = if i ∈ s then character s x else 0 := by
  rw [halfDiff_character]
  split_ifs with hi
  · exact character_erase s x i hi
  · ring

lemma generator_zero_character {n : ℕ} (s : Finset (Fin n)) :
    generatorCLM (0 : Interaction n) (character s) = -(s.card : ℝ) • character s := by
  funext x
  change generator (0 : Interaction n) (character s) x = -(s.card : ℝ) * character s x
  simp only [generator, mean_zero, zero_sub, neg_mul, spin_mul_halfDiff_character,
    Finset.sum_neg_distrib]
  simp

theorem exp_apply_of_eigenvector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A : E →L[ℝ] E) (f : E) (a : ℝ)
    (h : A f = a • f) : NormedSpace.exp A f = Real.exp a • f := by
  have hp (k : ℕ) : (A ^ k) f = a ^ k • f := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, pow_succ]
  have hs : HasSum (fun k : ℕ => (k.factorial : ℝ)⁻¹ * a ^ k) (Real.exp a) := by
    simpa only [smul_eq_mul, Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a)
  apply (exp_apply_hasSum A f).unique
  simpa only [hp, smul_smul] using hs.smul_const f

lemma semigroup_zero_character {n : ℕ} (s : Finset (Fin n)) (t : ℝ) :
    semigroup (0 : Interaction n) t (character s) =
      Real.exp (-t * (s.card : ℝ)) • character s := by
  apply exp_apply_of_eigenvector
  rw [smul_apply, generator_zero_character, smul_smul]
  congr 1
  ring

lemma attempt_zero_character {n : ℕ} (s : Finset (Fin n)) :
    attemptLM (0 : Interaction n) (character s) =
      (1 - (s.card : ℝ) / n) • character s := by
  change character s + (n : ℝ)⁻¹ • generatorCLM (0 : Interaction n) (character s) = _
  rw [generator_zero_character, smul_smul]
  module

lemma attempt_pow_zero_character {n : ℕ} (s : Finset (Fin n)) (k : ℕ) :
    (attemptLM (0 : Interaction n) ^ k) (character s) =
      (1 - (s.card : ℝ) / n) ^ k • character s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, map_smul, attempt_zero_character,
      smul_smul, pow_succ]

lemma character_eq_prod_univ {n : ℕ} (s : Finset (Fin n)) (x : Spin n) :
    character s x = ∏ i : Fin n, if i ∈ s then spin x i else 1 := by
  simp [character, Finset.prod_ite_mem]

lemma character_inner {n : ℕ} (s r : Finset (Fin n)) :
    ∑ x : Spin n, character s x * character r x =
      if s = r then (2 : ℝ) ^ n else 0 := by
  by_cases h : s = r
  · subst r
    simp only [← pow_two, character_sq, ↓reduceIte, Finset.sum_const,
      Finset.card_univ, card_spin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [ite_eq_right h]
    have hp : (∑ x : Spin n, character s x * character r x) =
        ∏ i : Fin n, ∑ b : Bool,
          (if i ∈ s then (if b then (1 : ℝ) else -1) else 1) *
          (if i ∈ r then (if b then (1 : ℝ) else -1) else 1) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [character_eq_prod_univ, character_eq_prod_univ, ← Finset.prod_mul_distrib]
      rfl
    rw [hp]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ s ↔ i ∈ r) := by
      by_contra! hc
      exact h (Finset.ext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hs : i ∈ s <;> by_cases hr : i ∈ r
    · exact (hi (by simp [hs, hr])).elim
    · simp [hs, hr]
    · simp [hs, hr]
    · exact (hi (by simp [hs, hr])).elim

lemma character_sum {n : ℕ} (s : Finset (Fin n)) :
    ∑ x : Spin n, character s x = if s = ∅ then (2 : ℝ) ^ n else 0 := by
  simpa only [character_empty, mul_one] using character_inner s ∅

lemma character_delta_sum {n : ℕ} (x y : Spin n) :
    ∑ s : Finset (Fin n), character s x * character s y =
      if x = y then (2 : ℝ) ^ n else 0 := by
  have hsum : (∑ s : Finset (Fin n), character s x * character s y) =
      ∏ i : Fin n, (spin x i * spin y i + 1) := by
    rw [Finset.prod_add_one]
    simp only [Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.prod_mul_distrib (f := spin x) (g := spin y)).symm
  rw [hsum]
  by_cases h : x = y
  · subst y
    simp only [spin_mul_self, ↓reduceIte, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold spin
    cases hx : x i <;> cases hy : y i <;> simp_all

lemma delta_character_expansion {n : ℕ} (y : Spin n) :
    (fun x : Spin n => if x = y then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ n)⁻¹ • ∑ s : Finset (Fin n), character s y • character s := by
  funext x
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [mul_comm (character _ y)]
  rw [character_delta_sum]
  split_ifs <;> simp

lemma character_parseval {n : ℕ} (a : Finset (Fin n) → ℝ) :
    (∑ x : Spin n, (∑ s : Finset (Fin n), a s * character s x) ^ 2) =
      (2 : ℝ) ^ n * ∑ s : Finset (Fin n), a s ^ 2 := by
  simp only [pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (Finset.mul_sum ..).symm
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  simp_rw [show ∀ r x, a s * character s x * (a r * character r x) =
    (a s * a r) * (character s x * character r x) by intros; ring,
    ← Finset.mul_sum, character_inner]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq]
  ring

noncomputable def fourierKernel {n : ℕ} (a : Finset (Fin n) → ℝ)
    (x y : Spin n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ s : Finset (Fin n), a s * character s x * character s y

lemma continuousKernel_zero_fourier {n : ℕ} (t : ℝ) (x y : Spin n) :
    continuousKernel (0 : Interaction n) t x y =
      fourierKernel (fun s => Real.exp (-t * (s.card : ℝ))) x y := by
  unfold continuousKernel
  rw [delta_character_expansion y, map_smul, map_sum]
  simp_rw [map_smul, semigroup_zero_character]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, fourierKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

lemma discreteKernel_zero_fourier {n : ℕ} (k : ℕ) (x y : Spin n) :
    discreteKernel (0 : Interaction n) k x y =
      fourierKernel (fun s => (1 - (s.card : ℝ) / n) ^ k) x y := by
  unfold discreteKernel
  rw [delta_character_expansion y, map_smul, map_sum]
  simp_rw [map_smul, attempt_pow_zero_character]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, fourierKernel]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

noncomputable def centeredFourier {n : ℕ} (a : Finset (Fin n) → ℝ)
    (s : Finset (Fin n)) : ℝ := a s - if s = ∅ then 1 else 0

lemma centeredFourier_sum_sq {n : ℕ} (a : Finset (Fin n) → ℝ) (ha : a ∅ = 1) :
    ∑ s, centeredFourier a s ^ 2 = (∑ s, a s ^ 2) - 1 := by
  have h (s : Finset (Fin n)) : centeredFourier a s ^ 2 =
      a s ^ 2 - if s = ∅ then 1 else 0 := by
    by_cases hs : s = ∅ <;> simp [centeredFourier, hs, ha]
  simp_rw [h, Finset.sum_sub_distrib]
  simp

lemma centeredFourier_expansion {n : ℕ} (a : Finset (Fin n) → ℝ) (x y : Spin n) :
    ∑ s, centeredFourier a s * character s x * character s y =
      (∑ s, a s * character s x * character s y) - 1 := by
  simp only [centeredFourier, sub_mul, Finset.sum_sub_distrib]
  simp

lemma fourierKernel_sub_uniform {n : ℕ} (a : Finset (Fin n) → ℝ) (x y : Spin n) :
    fourierKernel a x y - ((2 : ℝ) ^ n)⁻¹ =
      ((2 : ℝ) ^ n)⁻¹ * ∑ s, centeredFourier a s * character s x * character s y := by
  rw [centeredFourier_expansion]
  unfold fourierKernel
  ring

lemma fourierKernel_chiSquare {n : ℕ} (a : Finset (Fin n) → ℝ) (ha : a ∅ = 1)
    (x : Spin n) :
    (2 : ℝ) ^ n * ∑ y, (fourierKernel a x y - ((2 : ℝ) ^ n)⁻¹) ^ 2 =
      (∑ s, a s ^ 2) - 1 := by
  simp_rw [fourierKernel_sub_uniform, mul_pow]
  rw [← Finset.mul_sum, character_parseval]
  simp only [mul_pow, character_sq, mul_one]
  rw [centeredFourier_sum_sq a ha]
  field_simp

lemma totalVariation_fourier_sq_le {n : ℕ} (a : Finset (Fin n) → ℝ)
    (ha : a ∅ = 1) (x : Spin n) :
    4 * totalVariation (fourierKernel a x) (gibbs (0 : Interaction n)) ^ 2 ≤
      (∑ s, a s ^ 2) - 1 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun y : Spin n => |fourierKernel a x y - ((2 : ℝ) ^ n)⁻¹|) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, card_spin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one, sq_abs] at hc
  rw [mul_comm, fourierKernel_chiSquare a ha x] at hc
  simp only [totalVariation, gibbs_zero]
  nlinarith

lemma sum_pow_card {n : ℕ} (q : ℝ) :
    ∑ s : Finset (Fin n), q ^ s.card = (1 + q) ^ n := by
  simpa only [Finset.powerset_univ, one_pow, mul_one, Finset.card_univ,
    Fintype.card_fin, add_comm] using
    (Finset.sum_pow_mul_eq_add_pow q 1 (Finset.univ : Finset (Fin n)))

lemma exp_card_sq (t : ℝ) (k : ℕ) :
    Real.exp (-t * (k : ℝ)) ^ 2 = Real.exp (-2 * t) ^ k := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma continuous_zero_tv_sq_le {n : ℕ} (t : ℝ) (x : Spin n) :
    4 * totalVariation (continuousKernel (0 : Interaction n) t x)
      (gibbs (0 : Interaction n)) ^ 2 ≤ (1 + Real.exp (-2 * t)) ^ n - 1 := by
  have hkernel : continuousKernel (0 : Interaction n) t x =
      fourierKernel (fun s => Real.exp (-t * (s.card : ℝ))) x := by
    funext y; exact continuousKernel_zero_fourier t x y
  rw [hkernel]
  have h := totalVariation_fourier_sq_le (fun s => Real.exp (-t * (s.card : ℝ)))
    (by simp) x
  simpa only [exp_card_sq, sum_pow_card] using h

lemma discrete_character_sq_le {n : ℕ} (hn : 0 < n) (k : ℕ)
    (s : Finset (Fin n)) :
    ((1 - (s.card : ℝ) / n) ^ k) ^ 2 ≤ Real.exp (-2 * (k : ℝ) / n) ^ s.card := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (s.card : ℝ) ≤ n := by
    exact_mod_cast (show s.card ≤ n by simpa using Finset.card_le_univ s)
  have hnonneg : 0 ≤ 1 - (s.card : ℝ) / n := sub_nonneg.mpr ((div_le_one hn').mpr hc)
  have hle : 1 - (s.card : ℝ) / n ≤ Real.exp (-(s.card : ℝ) / n) := by
    simpa only [neg_div, sub_eq_add_neg, add_comm] using
      Real.add_one_le_exp (-(s.card : ℝ) / n)
  calc
    ((1 - (s.card : ℝ) / n) ^ k) ^ 2 =
        (1 - (s.card : ℝ) / n) ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ Real.exp (-(s.card : ℝ) / n) ^ (2 * k) := pow_le_pow_left₀ hnonneg hle _
    _ = Real.exp (-2 * (k : ℝ) / n) ^ s.card := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

lemma discrete_zero_tv_sq_le {n : ℕ} (hn : 0 < n) (k : ℕ) (x : Spin n) :
    4 * totalVariation (discreteKernel (0 : Interaction n) k x)
      (gibbs (0 : Interaction n)) ^ 2 ≤
      (1 + Real.exp (-2 * (k : ℝ) / n)) ^ n - 1 := by
  have hkernel : discreteKernel (0 : Interaction n) k x =
      fourierKernel (fun s => (1 - (s.card : ℝ) / n) ^ k) x := by
    funext y; exact discreteKernel_zero_fourier k x y
  rw [hkernel]
  apply (totalVariation_fourier_sq_le (fun s => (1 - (s.card : ℝ) / n) ^ k)
    (by simp) x).trans
  apply sub_le_sub_right _ 1
  rw [← sum_pow_card]
  exact Finset.sum_le_sum (fun s _ => discrete_character_sq_le hn k s)

end SKGapCutoff
end

end OAI
