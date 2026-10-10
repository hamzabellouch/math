import Mathlib
import OAI.Probability.LogConcave.LowerBounds.Theta

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open WithLp
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Matrix
open scoped BigOperators
open Polynomial

namespace LogConcaveSampling.LowerBound

def weightedEvaluation {κ : Type*} (c g : κ → ℝ) : ℝ[X] →ₗ[ℝ] (κ → ℝ) where
  toFun p k := g k * p.eval (c k)
  map_add' p q := by ext k; simp [Polynomial.eval_add, mul_add]
  map_smul' a p := by ext k; simp [Polynomial.eval_smul]; ring

def spectralPowers : Polynomial.Sequence ℝ where
  elems' n := ((Polynomial.X + Polynomial.C 3) * Polynomial.C (1 / 2 : ℝ)) ^ n
  degree_eq' n := by
    rw [Polynomial.degree_pow, Polynomial.degree_mul_C (by norm_num), Polynomial.degree_X_add_C]
    simp

theorem spectral_power_span_eq_cosine_span {κ : Type*} (angles g : κ → ℝ) (q : ℕ) :
    Submodule.span ℝ {v : κ → ℝ | ∃ j ≤ q,
      v = fun k => g k * ((3 + Real.cos (angles k)) / 2) ^ j} =
    Submodule.span ℝ {v : κ → ℝ | ∃ j ≤ q,
      v = fun k => g k * Real.cos ((j : ℝ) * angles k)} := by
  let ev := weightedEvaluation (fun k => Real.cos (angles k)) g
  let T := Polynomial.Chebyshev.chebyshevTsequence ℝ
  have hp := spectralPowers.span_degreeLE (m := q) (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (spectralPowers.ne_zero i)))
  have ht := T.span_degreeLE (m := q) (fun i _ =>
    isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (T.ne_zero i)))
  have heq := congrArg (Submodule.map ev) (hp.trans ht.symm)
  rw [Submodule.map_span, Submodule.map_span] at heq
  convert! heq using 1
  · congr 1
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨spectralPowers j, ⟨j, hj, rfl⟩, ?_⟩
      ext k
      simp only [ev, weightedEvaluation, spectralPowers,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      congr 2
      ring
    · rintro ⟨p, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      ext k
      simp only [ev, weightedEvaluation, spectralPowers,
        LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      congr 2
      ring
  · congr 1
    ext v
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨T j, ⟨j, hj, rfl⟩, ?_⟩
      ext k
      simp [ev, weightedEvaluation, T, Polynomial.Chebyshev.chebyshevTsequence,
        Polynomial.Chebyshev.T_real_cos]
    · rintro ⟨p, ⟨j, hj, rfl⟩, rfl⟩
      refine ⟨j, hj, ?_⟩
      ext k
      simp [ev, weightedEvaluation, T, Polynomial.Chebyshev.chebyshevTsequence,
        Polynomial.Chebyshev.T_real_cos]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev BlockIndex (q : ℕ) := Fin (q+1) × Fin (q+1)

def blockMatrix {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) : Matrix (Fin d) (BlockIndex q) ℝ :=
  fun k ij => cosineColumn d ij.2 k * x k ij.1

def blockCoefficient (d q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) (k : Fin d) : ℝ :=
  (if v.1 then weight d (2*q+1) k else 1) * cosineColumn d v.2.1.2 k * cosineColumn d v.2.2.2 k

def blockLeft (q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) : Fin (q+1) := v.2.1.1

def blockRight (q : ℕ) (v : Bool × BlockIndex q × BlockIndex q) : Fin (q+1) := v.2.2.1

theorem blockCoefficient_bound {d q : ℕ} (hd : 0 < d)
    (v : Bool × BlockIndex q × BlockIndex q) (k : Fin d) : |blockCoefficient d q v k| ≤ 2 / d := by
  obtain ⟨t, i, j⟩ := v
  cases t
  · simpa [blockCoefficient] using cosineColumn_product_le (j := i.2) (l := j.2) (k := k) hd
  · simp only [blockCoefficient, ↓reduceIte]
    rw [mul_assoc, abs_mul]
    calc
      _ ≤ 1 * |cosineColumn d i.2 k * cosineColumn d j.2 k| :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ _ := by simpa using cosineColumn_product_le (j := i.2) (l := j.2) (k := k) hd

theorem blockCoefficient_sum {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (v : Bool × BlockIndex q × BlockIndex q) :
    ∑ k, blockCoefficient d q v k =
      if v.1 then 0 else if v.2.1.2 = v.2.2.2 then 1 else 0 := by
  have hd : 0 < d := by omega
  have hj : (v.2.1.2 : ℕ) ≤ q := by omega
  have hl : (v.2.2.2 : ℕ) ≤ q := by omega
  obtain ⟨t, i, j⟩ := v
  cases t
  · simp only [blockCoefficient, Bool.false_eq_true, ↓reduceIte, one_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => cosineColumn d i.2 k * cosineColumn d j.2 k) d]
    have h := cosineColumn_orthonormal hd
      (by have := i.2.isLt; omega : (i.2 : ℕ) < d)
      (by have := j.2.isLt; omega : (j.2 : ℕ) < d)
    simpa only [Fin.ext_iff] using h
  · simp only [blockCoefficient, ↓reduceIte]
    rw [Fin.sum_univ_eq_sum_range (fun k => weight d (2*q+1) k * cosineColumn d i.2 k * cosineColumn d j.2 k) d]
    exact cosineColumn_weighted_orthogonal hj hl hqd

theorem blockGram_entry {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) (i j : BlockIndex q) :
    ((blockMatrix x).transpose * blockMatrix x) i j =
      gaussianRowSum (blockCoefficient d q (false,i,j)) i.1 j.1 x := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, blockMatrix, blockCoefficient,
    Bool.false_eq_true, ↓reduceIte, one_mul, gaussianRowSum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem blockWeightedGram_entry {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) (i j : BlockIndex q) :
    ((blockMatrix x).transpose * Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x) i j =
      gaussianRowSum (blockCoefficient d q (true,i,j)) i.1 j.1 x := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, blockMatrix,
    blockCoefficient, ↓reduceIte, gaussianRowSum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem block_total_energy_eq {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (x : Fin d → Fin (q+1) → ℝ) :
    matrixEnergy ((blockMatrix x).transpose * blockMatrix x - 1) +
      matrixEnergy ((blockMatrix x).transpose * Matrix.diagonal
        (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x) =
      rowDeviationEnergy (blockCoefficient d q) (blockLeft q) (blockRight q) x := by
  have heq (i j : BlockIndex q) : (if i = j then (1 : ℝ) else 0) =
      (if i.1 = j.1 then 1 else 0) * (if i.2 = j.2 then 1 else 0) := by
    obtain ⟨i,a⟩ := i
    obtain ⟨j,b⟩ := j
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [matrixEnergy, rowDeviationEnergy, Matrix.sub_apply, Matrix.one_apply,
    blockGram_entry, blockWeightedGram_entry, heq,
    Fintype.sum_prod_type, Fintype.sum_bool, blockLeft, blockRight,
    blockCoefficient_sum hqd, Bool.false_eq_true, ↓reduceIte, mul_zero, sub_zero]
  rw [add_comm]
  rfl

theorem block_total_energy_mean_le {d q : ℕ} (hqd : 4*q+1 < 2*d) :
    ∫ x, (matrixEnergy ((blockMatrix x).transpose * blockMatrix x - 1) +
      matrixEnergy ((blockMatrix x).transpose * Matrix.diagonal
        (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x)) ∂gaussianRows d (q+1) ≤
      16 * ((q : ℝ)+1)^4 / d := by
  simp_rw [block_total_energy_eq hqd]
  have h := rowDeviationEnergy_mean_le (by omega : 0 < d) (blockCoefficient d q)
    (blockLeft q) (blockRight q) (blockCoefficient_bound (by omega))
  convert! h using 1
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, BlockIndex]
  ring

def blockTolerance (d q : ℕ) : ℝ := 40 * ((q : ℝ) + 1)^2 / Real.sqrt d

theorem blockTolerance_pos {d q : ℕ} (hd : 0 < d) : 0 < blockTolerance d q := by
  unfold blockTolerance
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

theorem block_good_event {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (hτ : blockTolerance d q ≤ 1/2) :
    ∃ G : Set (Fin d → Fin (q+1) → ℝ), MeasurableSet G ∧
      (99 : ℝ)/100 ≤ (gaussianRows d (q+1)).real G ∧
      ∀ x ∈ G, ∀ u ∈ Submodule.span ℝ (Set.range (blockMatrix x).col),
        |dotProduct u (Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) *ᵥ u)| ≤
          2 * blockTolerance d q * dotProduct u u := by
  have hd : 0 < d := by omega
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have htpos := blockTolerance_pos (q := q) hd
  let E := rowDeviationEnergy (blockCoefficient d q) (blockLeft q) (blockRight q)
  have hE := rowDeviationEnergy_measurable (blockCoefficient d q) (blockLeft q) (blockRight q)
  let G : Set (Fin d → Fin (q+1) → ℝ) := {x | E x < (blockTolerance d q)^2}
  have hG : MeasurableSet G := hE measurableSet_Iio
  refine ⟨G,hG,?_,?_⟩
  · have hbad := rowDeviationEnergy_tail hd (blockCoefficient d q) (blockLeft q)
      (blockRight q) (blockCoefficient_bound hd) (sq_pos_of_pos htpos)
    have hconst : (8 * (Fintype.card (Bool × BlockIndex q × BlockIndex q) : ℝ) / d) /
        (blockTolerance d q)^2 = 1/100 := by
      simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, BlockIndex,
        blockTolerance, div_pow, Real.sq_sqrt hdr.le]
      have hq : (q : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hconst] at hbad
    have hcompl : Gᶜ = {x | (blockTolerance d q)^2 ≤ E x} := by ext x; simp [G]
    have hm := measureReal_compl hG (μ := gaussianRows d (q+1))
    rw [probReal_univ, hcompl] at hm
    change (gaussianRows d (q+1)).real {x | (blockTolerance d q)^2 ≤ E x} ≤ 1/100 at hbad
    linarith
  · intro x hx
    have hx' : E x < (blockTolerance d q)^2 := hx
    have he := block_total_energy_eq hqd x
    have h₁ := matrixEnergy_nonneg ((blockMatrix x).transpose * blockMatrix x - 1)
    have h₂ := matrixEnergy_nonneg ((blockMatrix x).transpose * Matrix.diagonal
      (fun k : Fin d => weight d (2*q+1) k) * blockMatrix x)
    apply gram_control_on_column_span (blockMatrix x) _ htpos.le hτ
    · change _ = E x at he
      linarith
    · change _ = E x at he
      linarith

def krylovSpace {d q : ℕ} (x : Fin d → Fin (q+1) → ℝ) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ {v | ∃ i : Fin (q+1), ∃ j : ℕ, j ≤ q ∧
    v = fun k => x k i * eigenvalue d k ^ j}

theorem block_span_eq_krylov {d q : ℕ} (hd : 0 < d) (x : Fin d → Fin (q+1) → ℝ) :
    Submodule.span ℝ (Set.range (blockMatrix x).col) = krylovSpace x := by
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  have heq (i : Fin (q+1)) := spectral_power_span_eq_cosine_span
    (fun k : Fin d => theta d k) (fun k => x k i) q
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨⟨i,j⟩,rfl⟩
    have hcos : (fun k : Fin d => x k i * Real.cos ((j : ℝ) * theta d k)) ∈
        Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
          v = fun k => x k i * Real.cos ((l : ℝ) * theta d k)} :=
      Submodule.subset_span ⟨j,by omega,rfl⟩
    rw [← heq i] at hcos
    have hle : Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
        v = fun k => x k i * ((3 + Real.cos (theta d k))/2)^l} ≤ krylovSpace x := by
      apply Submodule.span_le.mpr
      rintro v ⟨l,hl,rfl⟩
      exact Submodule.subset_span ⟨i,l,hl,rfl⟩
    have h := (krylovSpace x).smul_mem (cosineAmplitude j / Real.sqrt d) (hle hcos)
    convert! h using 1
    ext k
    simp only [Matrix.col, Matrix.transpose_apply, blockMatrix, cosineColumn, Pi.smul_apply, smul_eq_mul]
    ring
  · apply Submodule.span_le.mpr
    rintro v ⟨i,j,hj,rfl⟩
    have hpow : (fun k : Fin d => x k i * eigenvalue d k ^ j) ∈
        Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
          v = fun k => x k i * ((3 + Real.cos (theta d k))/2)^l} :=
      Submodule.subset_span ⟨j,hj,rfl⟩
    rw [heq i] at hpow
    have hle : Submodule.span ℝ {v : Fin d → ℝ | ∃ l ≤ q,
        v = fun k => x k i * Real.cos ((l : ℝ) * theta d k)} ≤
        Submodule.span ℝ (Set.range (blockMatrix x).col) := by
      apply Submodule.span_le.mpr
      rintro v ⟨l,hl,rfl⟩
      have ha : cosineAmplitude l ≠ 0 := (cosineAmplitude_pos l).ne'
      have h := (Submodule.span ℝ (Set.range (blockMatrix x).col)).smul_mem
        (Real.sqrt d / cosineAmplitude l)
        (Submodule.subset_span (Set.mem_range_self (i, (⟨l,by omega⟩ : Fin (q+1)))))
      convert! h using 1
      ext k
      simp only [Matrix.col, Matrix.transpose_apply, blockMatrix, cosineColumn, Pi.smul_apply, smul_eq_mul]
      field_simp
    exact hle hpow

theorem lower_span_statistic {d q : ℕ} (hqd : 4*q+1 < 2*d)
    (hτ : blockTolerance d q ≤ 1/2) :
    ∃ G : Set (Fin d → Fin (q+1) → ℝ), MeasurableSet G ∧
      (99 : ℝ)/100 ≤ (gaussianRows d (q+1)).real G ∧
      ∀ x ∈ G, ∀ u ∈ krylovSpace x,
        |dotProduct u (Matrix.diagonal (fun k : Fin d => weight d (2*q+1) k) *ᵥ u)| ≤
          2 * blockTolerance d q * dotProduct u u := by
  obtain ⟨G,hG,hm,hu⟩ := block_good_event hqd hτ
  refine ⟨G,hG,hm,?_⟩
  intro x hx u hu'
  apply hu x hx u
  rw [block_span_eq_krylov (by omega)]
  exact hu'

end LogConcaveSampling.LowerBound

open scoped BigOperators

namespace LogConcaveSampling.LowerBound

def spectralDecay : ℝ := 3 - 2 * Real.sqrt 2

theorem spectralDecay_pos : 0 < spectralDecay := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [spectralDecay]
  nlinarith [Real.sqrt_nonneg 2]

theorem spectralDecay_lt_one : spectralDecay < 1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [spectralDecay]
  nlinarith [Real.sqrt_nonneg 2]

theorem hasSum_geometric_cos {t : ℝ} (ht : |t| < 1) (θ : ℝ) :
    HasSum (fun j : ℕ => t ^ j * Real.cos ((j : ℝ) * θ))
      ((1 - t * Real.cos θ) / (1 - 2 * t * Real.cos θ + t ^ 2)) := by
  let z : ℂ := (t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hz : ‖z‖ < 1 := by
    simpa [z, norm_mul, Complex.norm_exp] using ht
  have hs := Complex.hasSum_re (hasSum_geometric_of_norm_lt_one hz)
  have hterm : ∀ j : ℕ, (z ^ j).re = t ^ j * Real.cos ((j : ℝ) * θ) := by
    intro j
    have hexp : Complex.exp ((θ : ℂ) * Complex.I) ^ j =
        Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp only [z, mul_pow, hexp, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  simp_rw [hterm] at hs
  convert! hs using 1
  rw [Complex.inv_re]
  simp only [z, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.exp_ofReal_mul_I_re, Complex.normSq_apply,
    Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.exp_ofReal_mul_I_im]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem reciprocal_spectrum_fourier (θ : ℝ) :
    2 / (3 + Real.cos θ) =
      (1 / Real.sqrt 2) *
        (2 * (∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * θ)) - 1) := by
  have ht : |-spectralDecay| < 1 := by
    rw [abs_neg, abs_of_pos spectralDecay_pos]
    exact spectralDecay_lt_one
  rw [(hasSum_geometric_cos ht θ).tsum_eq]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)
  have hc : 0 < 3 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
  have hd : 0 < 1 - 2 * (-spectralDecay) * Real.cos θ + (-spectralDecay) ^ 2 := by
    have h := Real.neg_one_le_cos θ
    have hr := spectralDecay_pos
    have hr' := spectralDecay_lt_one
    nlinarith [sq_pos_of_pos (show 0 < 1 - spectralDecay by linarith)]
  have hr : 1 + spectralDecay ^ 2 = 6 * spectralDecay := by
    dsimp [spectralDecay]
    nlinarith
  have hr' : 1 - spectralDecay ^ 2 = 4 * Real.sqrt 2 * spectralDecay := by
    dsimp [spectralDecay]
    nlinarith
  symm
  calc
    _ = (1 - spectralDecay ^ 2) /
        (Real.sqrt 2 * (1 - 2 * (-spectralDecay) * Real.cos θ + (-spectralDecay) ^ 2)) := by
      have hd' : 1 + spectralDecay * Real.cos θ * 2 + spectralDecay ^ 2 ≠ 0 := by nlinarith
      ring_nf
      field_simp [hp.ne', hd']
      ring
    _ = (4 * Real.sqrt 2 * spectralDecay) /
        (Real.sqrt 2 * (2 * spectralDecay * (3 + Real.cos θ))) := by
      rw [hr']
      congr 2
      nlinarith
    _ = 2 / (3 + Real.cos θ) := by
      field_simp [hp.ne', spectralDecay_pos.ne', hc.ne']
      ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def cosineCorrelation (d n j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range d, Real.cos ((n : ℝ) * theta d k) * Real.cos ((j : ℝ) * theta d k)

theorem cosineCorrelation_abs_le (d n j : ℕ) : |cosineCorrelation d n j| ≤ d := by
  unfold cosineCorrelation
  calc
    _ ≤ ∑ k ∈ Finset.range d,
        |Real.cos ((n : ℝ) * theta d k) * Real.cos ((j : ℝ) * theta d k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_cos_le_one _)
    _ = _ := by simp

theorem cosineCorrelation_diagonal {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    cosineCorrelation d n n = (d : ℝ) / 2 := by
  simpa only [cosineCorrelation, ← pow_two] using sum_half_grid_cos_sq hn hnd

theorem cosineCorrelation_zero {d n j : ℕ} (hne : n ≠ j) (hjn : n + j < 2 * d) :
    cosineCorrelation d n j = 0 := sum_half_grid_cos_mul hne hjn

theorem summable_weighted_cosineCorrelation (d n N : ℕ) :
    Summable (fun j : ℕ => (-spectralDecay) ^ (j + N) * cosineCorrelation d n (j + N)) := by
  have hg := (summable_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one).mul_left
    ((d : ℝ) * spectralDecay ^ N)
  apply hg.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos spectralDecay_pos]
  calc
    _ ≤ spectralDecay ^ (j+N) * d :=
      mul_le_mul_of_nonneg_left (cosineCorrelation_abs_le d n (j+N)) (pow_nonneg spectralDecay_pos.le _)
    _ = _ := by rw [pow_add]; ring

theorem reciprocal_spectrum_statistic_series {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    (∑ k ∈ Finset.range d, weight d n k / eigenvalue d k) =
      Real.sqrt 2 * ∑' j : ℕ, (-spectralDecay) ^ j * cosineCorrelation d n j := by
  have ht : |-spectralDecay| < 1 := by
    rw [abs_neg, abs_of_pos spectralDecay_pos]
    exact spectralDecay_lt_one
  have hswap : (∑' j : ℕ, (-spectralDecay) ^ j * cosineCorrelation d n j) =
      ∑ k ∈ Finset.range d, Real.cos ((n : ℝ) * theta d k) *
        ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k) := by
    simp only [cosineCorrelation, Finset.mul_sum]
    have hs := Summable.tsum_finsetSum (s := Finset.range d)
      (f := fun k (j : ℕ) => Real.cos ((n : ℝ) * theta d k) *
        ((-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)))
      (fun k _ => (hasSum_geometric_cos ht (theta d k)).summable.mul_left _)
    simp_rw [← mul_assoc] at hs
    convert! hs using 1
    · congr 1
      ext j
      apply Finset.sum_congr rfl
      intro k _
      ring
    · simp_rw [mul_assoc, tsum_mul_left]
  rw [hswap]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpoint : ∀ k : ℕ, weight d n k / eigenvalue d k =
      Real.sqrt 2 * (Real.cos ((n : ℝ) * theta d k) *
        ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)) -
      (1 / Real.sqrt 2) * Real.cos ((n : ℝ) * theta d k) := by
    intro k
    have hden : 0 < 3 + Real.cos (theta d k) := by linarith [Real.neg_one_le_cos (theta d k)]
    have h := reciprocal_spectrum_fourier (theta d k)
    unfold weight eigenvalue
    rw [div_div_eq_mul_div, mul_div_assoc, h]
    have hrel : 2 / Real.sqrt 2 = Real.sqrt 2 := by
      apply (div_eq_iff hsqrt_pos.ne').mpr
      nlinarith
    calc
      _ = (2 / Real.sqrt 2) * (Real.cos ((n : ℝ) * theta d k) *
            ∑' j : ℕ, (-spectralDecay) ^ j * Real.cos ((j : ℝ) * theta d k)) -
          (1 / Real.sqrt 2) * Real.cos ((n : ℝ) * theta d k) := by ring
      _ = _ := by rw [hrel]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_half_grid_cos_eq_zero hn (by omega), mul_zero, sub_zero]

theorem reciprocal_spectrum_statistic_initial_sum {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    (∑ j ∈ Finset.range (2*d-n), (-spectralDecay) ^ j * cosineCorrelation d n j) =
      (-spectralDecay) ^ n * ((d : ℝ) / 2) := by
  rw [Finset.sum_eq_single n]
  · rw [cosineCorrelation_diagonal hn hnd]
  · intro j hj hne
    rw [cosineCorrelation_zero (Ne.symm hne) (by have := Finset.mem_range.mp hj; omega), mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

theorem reciprocal_spectrum_statistic_remainder {d n : ℕ} (hn : 0 < n) (hnd : n < d) :
    |(∑ k ∈ Finset.range d, weight d n k / eigenvalue d k) -
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay) ^ n| ≤
      Real.sqrt 2 * d * spectralDecay ^ (2*d-n) / (1 - spectralDecay) := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsplit := (summable_weighted_cosineCorrelation d n 0).sum_add_tsum_nat_add (2*d-n)
  simp only [Nat.add_zero] at hsplit
  rw [reciprocal_spectrum_statistic_initial_sum hn hnd] at hsplit
  rw [reciprocal_spectrum_statistic_series hn hnd, ← hsplit]
  have hlead : Real.sqrt 2 * ((-spectralDecay)^n * ((d : ℝ)/2)) =
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^n := by
    field_simp
    rw [hsqrt]
    ring
  rw [mul_add, hlead, add_sub_cancel_left, abs_mul, abs_of_pos hsqrt_pos]
  have htail : |∑' j : ℕ, (-spectralDecay)^(j+(2*d-n)) * cosineCorrelation d n (j+(2*d-n))| ≤
      ((d : ℝ) * spectralDecay^(2*d-n)) / (1-spectralDecay) := by
    have hg := (summable_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one).mul_left
      ((d : ℝ) * spectralDecay^(2*d-n))
    calc
      _ ≤ ∑' j : ℕ, ‖(-spectralDecay) ^ (j+(2*d-n)) * cosineCorrelation d n (j+(2*d-n))‖ :=
        norm_tsum_le_tsum_norm (summable_weighted_cosineCorrelation d n (2*d-n)).norm
      _ ≤ ∑' j : ℕ, ((d : ℝ) * spectralDecay^(2*d-n)) * spectralDecay^j := by
        apply Summable.tsum_le_tsum _ (summable_weighted_cosineCorrelation d n (2*d-n)).norm hg
        intro j
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos spectralDecay_pos]
        calc
          _ ≤ spectralDecay^(j+(2*d-n)) * d :=
            mul_le_mul_of_nonneg_left (cosineCorrelation_abs_le d n _) (pow_nonneg spectralDecay_pos.le _)
          _ = _ := by rw [pow_add]; ring
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one spectralDecay_pos.le spectralDecay_lt_one]; rfl
  calc
    _ ≤ Real.sqrt 2 * (((d : ℝ) * spectralDecay^(2*d-n)) / (1-spectralDecay)) :=
      mul_le_mul_of_nonneg_left htail hsqrt_pos.le
    _ = _ := by ring

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def targetVariance (d k : ℕ) : ℝ≥0 :=
  ⟨(eigenvalue d k)⁻¹, inv_nonneg.mpr (by linarith [(eigenvalue_bounds d k).1])⟩

theorem targetVariance_le_one (d k : ℕ) : (targetVariance d k : ℝ) ≤ 1 := by
  change (eigenvalue d k)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (eigenvalue_bounds d k).1

def targetGaussian (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun k : Fin d => gaussianReal 0 (targetVariance d k))

instance targetGaussian_probability (d : ℕ) : IsProbabilityMeasure (targetGaussian d) := by
  unfold targetGaussian
  infer_instance

theorem targetGaussian_coordinate_law {d : ℕ} (k : Fin d) :
    HasLaw (fun x : Fin d → ℝ => x k) (gaussianReal 0 (targetVariance d k)) (targetGaussian d) :=
  (measurePreserving_eval (fun k : Fin d => gaussianReal 0 (targetVariance d k)) k).hasLaw

def diagonalStatistic {d : ℕ} (c : Fin d → ℝ) (u : Fin d → ℝ) : ℝ := ∑ k, c k * (u k)^2

theorem diagonalStatistic_memLp {d : ℕ} (c : Fin d → ℝ) :
    MemLp (diagonalStatistic c) 2 (targetGaussian d) := by
  apply memLp_finsetSum
  intro k _
  exact (gaussian_sq_memLp (targetGaussian_coordinate_law k)).const_mul (c k)

theorem targetGaussian_statistic_mean {d : ℕ} (c : Fin d → ℝ) :
    ∫ u, diagonalStatistic c u ∂targetGaussian d = ∑ k, c k / eigenvalue d k := by
  unfold diagonalStatistic
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, gaussian_integral_sq (targetGaussian_coordinate_law _)]
    rfl
  · intro k _
    exact ((gaussian_sq_memLp (targetGaussian_coordinate_law k)).const_mul (c k)).integrable
      (by norm_num)

theorem targetGaussian_statistic_variance {d : ℕ} (c : Fin d → ℝ) :
    Var[diagonalStatistic c; targetGaussian d] =
      ∑ k, (c k)^2 * (2 * ((targetVariance d k : ℝ)^2)) := by
  have h := variance_sum_pi (μ := fun k : Fin d => gaussianReal 0 (targetVariance d k))
    (X := fun k (y : ℝ) => c k * y^2)
    (fun k => (gaussian_sq_memLp (HasLaw.id (μ := gaussianReal 0 (targetVariance d k)))).const_mul (c k))
  have hvar (k : Fin d) : Var[fun y : ℝ => y^2; gaussianReal 0 (targetVariance d k)] =
      2 * (targetVariance d k : ℝ)^2 :=
    gaussian_sq_variance (X := fun y : ℝ => y) HasLaw.id
  simp only [variance_const_mul, hvar] at h
  convert! h using 1
  congr 1
  ext u
  simp [diagonalStatistic]

theorem targetGaussian_statistic_variance_le {d : ℕ} (c : Fin d → ℝ)
    (hc : ∀ k, |c k| ≤ 1) : Var[diagonalStatistic c; targetGaussian d] ≤ 2*d := by
  rw [targetGaussian_statistic_variance]
  calc
    _ ≤ ∑ _ : Fin d, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have hsq : (c k)^2 ≤ 1 := by simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (c k)) (by norm_num : (0 : ℝ) ≤ 1)).mpr (hc k)
      have hv := targetVariance_le_one d k
      have hn := (targetVariance d k).coe_nonneg
      have hv2 : (targetVariance d k : ℝ)^2 ≤ 1 := by nlinarith
      calc
        _ ≤ 1 * (2 * ((targetVariance d k : ℝ)^2)) := mul_le_mul_of_nonneg_right hsq (by positivity)
        _ ≤ 2 := by nlinarith
    _ = _ := by simp; ring

theorem targetGaussian_norm_mean_le (d : ℕ) :
    ∫ u, diagonalStatistic (fun _ : Fin d => 1) u ∂targetGaussian d ≤ d := by
  rw [targetGaussian_statistic_mean]
  calc
    _ ≤ ∑ _ : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      have h := targetVariance_le_one d k
      change (eigenvalue d k)⁻¹ ≤ 1 at h
      simpa only [one_div] using h
    _ = _ := by simp

theorem lower_target_statistic {d q : ℕ} (hn : 2*q+1 < d) :
    |(∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d) -
      (d : ℝ) / Real.sqrt 2 * (-spectralDecay)^(2*q+1)| ≤
        Real.sqrt 2 * d * spectralDecay^(2*d-(2*q+1)) / (1-spectralDecay) ∧
    Var[diagonalStatistic (fun k : Fin d => weight d (2*q+1) k); targetGaussian d] ≤ 2*d ∧
    (∫ u, diagonalStatistic (fun _ : Fin d => 1) u ∂targetGaussian d) ≤ d ∧
    Var[diagonalStatistic (fun _ : Fin d => 1); targetGaussian d] ≤ 2*d := by
  refine ⟨?_, targetGaussian_statistic_variance_le _ (fun _ => Real.abs_cos_le_one _),
    targetGaussian_norm_mean_le d, targetGaussian_statistic_variance_le _ (by simp)⟩
  rw [targetGaussian_statistic_mean,
    Fin.sum_univ_eq_sum_range (fun k => weight d (2*q+1) k / eigenvalue d k) d]
  exact reciprocal_spectrum_statistic_remainder (by omega) hn

theorem real_chebyshev {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω - ∫ z, X z ∂μ|} ≤ Var[X;μ] / c^2 := by
  have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top)
    (meas_ge_le_variance_div_sq hX hc)
  change (μ {ω | c ≤ |X ω - ∫ z, X z ∂μ|}).toReal ≤ _
  simpa only [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] using h

def separationThreshold (d q : ℕ) : ℝ := 160 * ((q : ℝ)+1)^2 * Real.sqrt d

def separationEvent (d q : ℕ) : Set (Fin d → ℝ) :=
  {u | diagonalStatistic (fun _ : Fin d => 1) u ≤ 2*d ∧
    separationThreshold d q < |diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u|}

theorem separationEvent_measurable (d q : ℕ) : MeasurableSet (separationEvent d q) := by
  have hN : Measurable (diagonalStatistic (fun _ : Fin d => 1)) := by
    unfold diagonalStatistic; fun_prop
  have hS : Measurable (diagonalStatistic (fun k : Fin d => weight d (2*q+1) k)) := by
    unfold diagonalStatistic; fun_prop
  exact (measurableSet_le hN measurable_const).inter (measurableSet_lt measurable_const hS.abs)

theorem target_separation_tail {d q : ℕ} (hd : 0 < d)
    (hsep : separationThreshold d q <
      |∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d|) :
    (targetGaussian d).real (separationEvent d q)ᶜ ≤ 2/(d : ℝ) +
      2*d / (|∫ u, diagonalStatistic (fun k : Fin d => weight d (2*q+1) k) u ∂targetGaussian d| -
        separationThreshold d q)^2 := by
  let N : (Fin d → ℝ) → ℝ := diagonalStatistic (fun _ : Fin d => 1)
  let S : (Fin d → ℝ) → ℝ := diagonalStatistic (fun k : Fin d => weight d (2*q+1) k)
  let m := ∫ u, S u ∂targetGaussian d
  let a := ∫ u, N u ∂targetGaussian d
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have ha : a ≤ d := targetGaussian_norm_mean_le d
  have hS : Var[S;targetGaussian d] ≤ 2*d :=
    targetGaussian_statistic_variance_le _ (fun _ => Real.abs_cos_le_one _)
  have hN : Var[N;targetGaussian d] ≤ 2*d :=
    targetGaussian_statistic_variance_le _ (by simp)
  have hrad : 0 < |m| - separationThreshold d q := sub_pos.mpr hsep
  have h₁ := real_chebyshev (diagonalStatistic_memLp (fun _ : Fin d => 1)) hdr
  have h₂ := real_chebyshev
    (diagonalStatistic_memLp (fun k : Fin d => weight d (2*q+1) k)) hrad
  have hsub : (separationEvent d q)ᶜ ⊆
      {u | (d : ℝ) ≤ |N u - a|} ∪ {u | |m| - separationThreshold d q ≤ |S u - m|} := by
    intro u hu
    change ¬ (N u ≤ 2*d ∧ separationThreshold d q < |S u|) at hu
    by_cases hnu : N u ≤ 2*d
    · right
      have hsu : |S u| ≤ separationThreshold d q := le_of_not_gt (fun h => hu ⟨hnu,h⟩)
      have habs := abs_sub_abs_le_abs_sub m (S u)
      rw [abs_sub_comm m (S u)] at habs
      change |m| - separationThreshold d q ≤ |S u-m|
      linarith only [habs,hsu]
    · left
      have habs := le_abs_self (N u-a)
      have hnu' := lt_of_not_ge hnu
      change (d : ℝ) ≤ |N u - a|
      linarith only [habs,hnu',ha]
  calc
    _ ≤ (targetGaussian d).real ({u | (d : ℝ) ≤ |N u-a|} ∪
        {u | |m|-separationThreshold d q ≤ |S u-m|}) := measureReal_mono hsub
    _ ≤ (targetGaussian d).real {u | (d : ℝ) ≤ |N u-a|} +
        (targetGaussian d).real {u | |m|-separationThreshold d q ≤ |S u-m|} :=
      measureReal_union_le _ _
    _ ≤ Var[N;targetGaussian d]/(d : ℝ)^2 +
        Var[S;targetGaussian d]/(|m|-separationThreshold d q)^2 := add_le_add h₁ h₂
    _ ≤ 2*d/(d : ℝ)^2 + 2*d/(|m|-separationThreshold d q)^2 := by
      exact add_le_add (div_le_div_of_nonneg_right hN (sq_nonneg _))
        (div_le_div_of_nonneg_right hS (sq_nonneg _))
    _ = _ := by
      congr 1
      field_simp

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
