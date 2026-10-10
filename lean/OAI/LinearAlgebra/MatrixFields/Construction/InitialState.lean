import Mathlib
import OAI.LinearAlgebra.MatrixFields.Arithmetic.ArithmeticExponent
import OAI.LinearAlgebra.MatrixFields.Construction.ComplexPolynomialWitnessProduct
import OAI.LinearAlgebra.MatrixFields.Construction.InitialHistories
import OAI.LinearAlgebra.MatrixFields.Entropy.RectangularGrowth
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryPositions

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem rectangularAdmissibleExponent_of_rankAtMost
    {a b R : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hτ : 0 ≤ τ) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_block_step
    (K := 2 * R * (2 * (a * b) + a ^ 2)) ha hk hab hτ hR hin hout
  · exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, (scalarAlgorithm_cost F).le⟩
  · intro m p P hP
    obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
    refine ⟨Q, hQ, ?_⟩
    rw [hcost]
    nlinarith [Nat.zero_le (2 * R * (2 * (a * b) * m ^ 2 + a ^ 2 * (m * p)))]

theorem rectangular_rpow_omega_le_of_rankAtMost
    {a b R : ℕ} {B k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ B) (hin : (a * b : ℕ) ≤ B)
    (hR : (R : ℝ) ≤ B) :
    (a : ℝ) ^ rectangularOmega F k ≤ B := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha1
  have hB : 0 < B := (sq_pos_of_pos ha0).trans_le hout
  have hpow : (a : ℝ) ^ Real.logb a B = B :=
    Real.rpow_logb ha0 (ne_of_gt ha1) hB
  have hτ : 2 ≤ Real.logb (a : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le ha1 hB).mpr
    simpa only [Real.rpow_two] using hout
  have hadm := rectangularAdmissibleExponent_of_rankAtMost ha hk hab hRank
    (by linarith : 0 ≤ Real.logb (a : ℝ) B)
    (hR.trans_eq hpow.symm) (hin.trans_eq hpow.symm) (hout.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le ha1.le
    (rectangularOmega_le_of_admissibleExponent hadm)).trans_eq hpow

theorem rectangular_rpow_omega_le_of_rank_growth
    {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
    (R : ℕ → ℕ)
    (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
        (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
    (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
    (a : ℝ) ^ rectangularOmega F k ≤ q := by
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hq0 : 0 ≤ q := (sq_nonneg (a : ℝ)).trans hout
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm ha0]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have hbase : ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) = ((a : ℝ) ^ (2 : ℕ)) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hinput : ((a ^ t * b ^ t : ℕ) : ℝ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t * b ^ t : ℕ) : ℝ) = (((a * b : ℕ) : ℝ)) ^ t := by
        simp only [Nat.cast_mul, Nat.cast_pow, mul_pow]
      _ ≤ q ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) hin t
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rectangular_rpow_omega_le_of_rankAtMost hat hk habt
    (hRank t) hbase hinput hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm ha0] using h

theorem equalRectangular_inequality {a b L r : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hbatch : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by
    have hbR : (0 : ℝ) < (b : ℝ) :=
      (Real.rpow_pos_of_pos (by exact_mod_cast ha0) k).trans_le hab
    exact_mod_cast hbR
  have hlower := Tensor.rectangular_directSum_rank_lower ha0 hb0 hbatch
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hout : (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * (a : ℝ) ^ (2 : ℕ) ≤ (r : ℝ) := by exact_mod_cast hlower.1
    simpa only [mul_comm] using hh
  have hin : ((a * b : ℕ) : ℝ) ≤ (r : ℝ) / (L : ℝ) := by
    apply (le_div_iff₀ hLR).mpr
    have hh : (L : ℝ) * ((a * b : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hlower.2
    simpa only [mul_comm] using hh
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hq : 1 < (r : ℝ) / (L : ℝ) := by nlinarith
  have hcost := affine_recurrence_bound (fun t => (batchRank L r t : ℝ))
    ((r : ℝ) / (L : ℝ)) (r : ℝ) hq (Nat.cast_nonneg r)
    (fun t => batchRank_succ_le_affine hL r t)
  have hbound : (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) / (L : ℝ) := by
    apply rectangular_rpow_omega_le_of_rank_growth
      (C := (batchRank L r 0 : ℝ) + (r : ℝ) / ((r : ℝ) / (L : ℝ) - 1))
      ha hk hab hout hin (batchRank L r)
    · exact Tensor.rectangular_pow_batchRank hL hbatch
    · intro t
      exact (hcost t).trans_eq (mul_comm _ _)
  simpa only [mul_comm] using (le_div_iff₀ hLR).mp hbound

theorem power_le_of_forall_pow_le_square_linear_mul_pow (d : ℕ) {x r : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → x ^ n ≤ ((d * n + 1 : ℕ) : ℝ) ^ 2 * r ^ n) :
    x ≤ r := by
  apply power_le_of_forall_pow_le_linear_mul_pow (2 * d) hr
  intro n hn
  apply le_of_pow_le_pow_left₀ (by decide : (2 : ℕ) ≠ 0)
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr n))
  have he := h (n * 2) (Nat.mul_pos hn (by decide))
  have hcount : d * (n * 2) + 1 = 2 * d * n + 1 := by ring
  simpa only [pow_mul, hcount, mul_pow] using he

theorem equalRectangular_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hk : 0 ≤ k) (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    (L : ℝ) * (a : ℝ) ^ rectangularOmega F k ≤ (r : ℝ) := by
  apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have h := equalRectangular_inequality hat hk habt
    (Tensor.rectangular_directSum_power_rank (FieldCoefficientExtraction.rank_power P t))
  simpa only [Nat.cast_pow, Nat.cast_mul, mul_pow,
    ← Real.rpow_pow_comm (Nat.cast_nonneg a)] using h

theorem equalRectangular_log_inequality_of_polynomialApproximation
    {a b L r d D : ℕ} {k : ℝ}
    (ha : 2 ≤ a) (hL : 0 < L) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin a))) r d D) :
    rectangularOmega F k * Real.log (a : ℝ) ≤ Real.log (r : ℝ) - Real.log (L : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow := Real.rpow_pos_of_pos ha0 (rectangularOmega F k)
  have hbound := equalRectangular_inequality_of_polynomialApproximation ha hk hab P
  have hlog := Real.log_le_log (mul_pos hL0 hpow) hbound
  rw [Real.log_mul (ne_of_gt hL0) (ne_of_gt hpow), Real.log_rpow ha0] at hlog
  linarith

theorem equalSquare_inequality_of_polynomialApproximation
    {n L r d D : ℕ} (hn : 1 ≤ n)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin n) (Fin n) (Fin n))) r d D) :
    (L : ℝ) * (n : ℝ) ^ omega F ≤ (r : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    apply power_le_of_forall_pow_le_square_linear_mul_pow d (Nat.cast_nonneg r)
    intro t ht
    have hrank := Tensor.rectangular_directSum_power_rank
      (FieldCoefficientExtraction.rank_power P t)
    have hlower := MatrixMultiplication.Foundation.Tensor.directSum_square_rank_lower
      (L ^ t) (1 ^ t) ((d * t + 1) ^ 2 * r ^ t) (by simp) hrank
    have hcast := (Nat.cast_le (α := ℝ)).mpr hlower
    simpa only [one_pow, mul_one, Nat.cast_mul, Nat.cast_pow] using hcast
  · have h := equalRectangular_inequality_of_polynomialApproximation
      (by omega : 2 ≤ n) (by norm_num : (0 : ℝ) ≤ 1)
      (by simp : (n : ℝ) ^ (1 : ℝ) ≤ (n : ℝ)) P
    simpa only [rectangularOmega_one] using h

theorem equalVolume_inequality_of_polynomialApproximation
    {a b c L r d D : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (P : MatrixMultiplication.Foundation.Tensor.PolynomialApproximation
      (MatrixMultiplication.Foundation.Tensor.directSum (fun _ : Fin L =>
        MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
          (Fin a) (Fin b) (Fin c))) r d D) :
    (L : ℝ) * ((a * b * c : ℕ) : ℝ) ^ (omega F / 3) ≤ (r : ℝ) := by
  let tags : Fin (L ^ 3) ≃ (Fin L × Fin L) × Fin L :=
    Fintype.equivOfCardEq (by simp [pow_succ])
  let indices : Fin (a * b * c) ≃ Fin a × Fin b × Fin c :=
    Fintype.equivOfCardEq (by simp [mul_assoc])
  have Q := P.matrixCoefficients_directSum_symmetrized.matrixCoefficients_directSum_of_injective
    tags tags.injective indices indices.injective
  have h := equalSquare_inequality_of_polynomialApproximation
    (Nat.mul_pos (Nat.mul_pos ha hb) hc) Q
  apply mul_rpow_third_le_of_cube (Nat.cast_nonneg (a * b * c)) (Nat.cast_nonneg r)
  simpa only [Nat.cast_pow] using h

end Arithmetic
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

structure AllFieldWitness (F : Type*) [Field F] where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  multiplicity : ℕ
  rankBound : ℕ
  order : ℕ
  degree : ℕ
  rows_pos : 0 < rows
  inner_pos : 0 < inner
  columns_pos : 0 < columns
  multiplicity_pos : 0 < multiplicity
  rankBound_pos : 0 < rankBound
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixCoefficients (K := F) (Fin rows) (Fin inner) (Fin columns)))
    rankBound order degree

namespace AllFieldWitness

variable {F : Type*} [Field F]

def volume (W : AllFieldWitness F) : ℕ := W.rows * W.inner * W.columns

theorem volume_pos (W : AllFieldWitness F) : 0 < W.volume :=
  Nat.mul_pos (Nat.mul_pos W.rows_pos W.inner_pos) W.columns_pos

theorem finite_inequality (W : AllFieldWitness F) :
    (W.multiplicity : ℝ) * (W.volume : ℝ) ^ (Arithmetic.omega F / 3) ≤ W.rankBound :=
  Arithmetic.equalVolume_inequality_of_polynomialApproximation
    W.rows_pos W.inner_pos W.columns_pos W.approximation

theorem log_inequality (W : AllFieldWitness F) :
    Real.log (W.multiplicity : ℝ) +
      (Arithmetic.omega F / 3) * Real.log (W.volume : ℝ) ≤
        Real.log (W.rankBound : ℝ) := by
  have hm : (0 : ℝ) < W.multiplicity := Nat.cast_pos.mpr W.multiplicity_pos
  have hv : (0 : ℝ) < W.volume := Nat.cast_pos.mpr W.volume_pos
  have hp := Real.rpow_pos_of_pos hv (Arithmetic.omega F / 3)
  have h := Real.log_le_log (mul_pos hm hp) W.finite_inequality
  rw [Real.log_mul hm.ne' hp.ne', Real.log_rpow hv] at h
  exact h

end AllFieldWitness
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.AllFieldSource

abbrev Word (K N : ℕ) := Fin (8 * K * N) → Fin 7

abbrev Index (Copies : Type*) (K N : ℕ) := Copies × Word K N

def tensor (F Copies : Type*) [CommRing F] [DecidableEq Copies] (K N : ℕ) :
    Tensor F (Index Copies K N) (Index Copies K N) (Index Copies K N) :=
  Tensor.directSum (fun _ : Copies => Tensor.power (FieldCW.tensor F 5) (8 * K * N))

def rankBudget (Copies : Type*) [Fintype Copies] (K N : ℕ) : ℕ :=
  Fintype.card Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N))

theorem rank_bound (F Copies : Type*) [Field F]
    [Fintype Copies] [DecidableEq Copies] (K N : ℕ) :
    Tensor.RankAtMost (tensor F Copies K N) (rankBudget Copies K N) := by
  have h := (Tensor.diagonal_rankAtMost (K := F) Copies).product
    (FieldCW.rank_power F 5 (8 * K * N))
  convert h using 1
  · funext x y z
    simp [tensor, Tensor.directSum, Tensor.product, Tensor.diagonal, ite_mul]
  · rfl

theorem rankBudget_pos (Copies : Type*) [Fintype Copies] (K N : ℕ)
    (hcopies : 0 < Fintype.card Copies) : 0 < rankBudget Copies K N := by
  unfold rankBudget
  exact Nat.mul_pos hcopies
    (Nat.mul_pos (pow_pos (Nat.succ_pos _) _) (pow_pos (by decide) _))

theorem rankBudget_prod (Slots Copies : Type*) [Fintype Slots] [Fintype Copies]
    (K N : ℕ) :
    rankBudget (Slots × Copies) K N = Fintype.card Slots * rankBudget Copies K N := by
  simp only [rankBudget, Fintype.card_prod, Nat.mul_assoc]

def matrixTarget (F : Type*) [CommSemiring F] (a b c L : ℕ) :=
  Tensor.directSum (fun _ : Fin L =>
    Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin c))

section Consumer

variable {F Copies : Type*} [Field F] [Fintype Copies] [DecidableEq Copies]
variable {K N a b c L : ℕ}

theorem restricted_rank_bound
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.RankAtMost (matrixTarget F a b c L) (rankBudget Copies K N) := by
  have heq : Tensor.restrict A B C (tensor F Copies K N) = matrixTarget F a b c L :=
    funext fun x => funext fun y => funext fun z => hcoeff x y z
  rw [← heq]
  exact (rank_bound F Copies K N).restrict A B C

def restrictedApproximation
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z) :
    Tensor.PolynomialApproximation (matrixTarget F a b c L) (rankBudget Copies K N) 0 0 :=
  Tensor.PolynomialApproximation.ofRankAtMost _ _ (restricted_rank_bound A B C hcoeff)

def ofRestriction
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z)
    (hcopies : 0 < Fintype.card Copies) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F where
  rows := a
  inner := b
  columns := c
  multiplicity := L
  rankBound := rankBudget Copies K N
  order := 0
  degree := 0
  rows_pos := ha
  inner_pos := hb
  columns_pos := hc
  multiplicity_pos := hL
  rankBound_pos := rankBudget_pos Copies K N hcopies
  approximation := restrictedApproximation A B C hcoeff

theorem ofRestriction_polynomial
    (A : (Fin L × (Fin a × Fin b)) → Index Copies K N → F)
    (B : (Fin L × (Fin b × Fin c)) → Index Copies K N → F)
    (C : (Fin L × (Fin c × Fin a)) → Index Copies K N → F)
    (hcoeff : ∀ x y z,
      Tensor.restrict A B C (tensor F Copies K N) x y z = matrixTarget F a b c L x y z)
    (hcopies : 0 < Fintype.card Copies) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hL : 0 < L) :
    (ofRestriction A B C hcoeff hcopies ha hb hc hL).approximation.polynomial =
      fun x y z => Polynomial.C (matrixTarget F a b c L x y z) := rfl

end Consumer

end MatrixMultiplication.AllFieldSource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {F : Type*} [Field F]

structure LocalMap {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    (source : Tensor F X Y Z) (target : Tensor F X' Y' Z') where
  x : X' → X → F
  y : Y' → Y → F
  z : Z' → Z → F
  coefficient : Tensor.restrict x y z source = target

namespace LocalMap

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type}
  [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype X'] [Fintype Y'] [Fintype Z']
  {source : Tensor F X Y Z} {middle : Tensor F X' Y' Z'}
  {target : Tensor F X'' Y'' Z''}

def identity (source : Tensor F X Y Z) : LocalMap source source where
  x := fun x s => if s = x then 1 else 0
  y := fun y s => if s = y then 1 else 0
  z := fun z s => if s = z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    rfl

def delete (source : Tensor F X Y Z) (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) :
    LocalMap source (ExactRecovery.delete source px py pz) where
  x := fun x s => if s = x ∧ px x then 1 else 0
  y := fun y s => if s = y ∧ py y then 1 else 0
  z := fun z s => if s = z ∧ pz z then 1 else 0
  coefficient := by
    funext x y z
    by_cases hx : px x <;> by_cases hy : py y <;> by_cases hz : pz z <;>
      simp [Tensor.restrict, ExactRecovery.delete, hx, hy, hz, ite_mul, mul_ite]

def product {U V W U' V' W' : Type}
    [Fintype U] [Fintype V] [Fintype W]
    {other : Tensor F U V W} {otherTarget : Tensor F U' V' W'}
    (first : LocalMap source middle) (second : LocalMap other otherTarget) :
    LocalMap (Tensor.product source other) (Tensor.product middle otherTarget) where
  x := fun x s => first.x x.1 s.1 * second.x x.2 s.2
  y := fun y s => first.y y.1 s.1 * second.y y.2 s.2
  z := fun z s => first.z z.1 s.1 * second.z z.2 s.2
  coefficient := by
    rw [Tensor.restrict_product, first.coefficient, second.coefficient]

def comp (first : LocalMap source middle) (second : LocalMap middle target) :
    LocalMap source target where
  x := Tensor.composeRestrictionMatrix second.x first.x
  y := Tensor.composeRestrictionMatrix second.y first.y
  z := Tensor.composeRestrictionMatrix second.z first.z
  coefficient := by
    rw [← Tensor.restrict_restrict, first.coefficient, second.coefficient]

def withSource (map : LocalMap source middle) (newSource : Tensor F X Y Z)
    (same : newSource = source) : LocalMap newSource middle where
  x := map.x
  y := map.y
  z := map.z
  coefficient := by rw [same]; exact map.coefficient

def ofExists
    (h : ∃ (a : X' → X → F) (b : Y' → Y → F) (c : Z' → Z → F),
      Tensor.restrict a b c source = middle) : LocalMap source middle := by
  choose a b c habc using h
  exact ⟨a, b, c, habc⟩

def parallelCopies (map : LocalMap source middle) (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => source))
      (Tensor.directSum (fun _ : R => middle)) where
  x := fun x s => if x.1 = s.1 then map.x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then map.y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then map.z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum (fun _ : R => source)
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
    simpa only [map.coefficient] using h

def directSum {I : Type} [Fintype I]
    (T : I → Tensor F X Y Z) (Q : I → Tensor F X' Y' Z')
    (maps : ∀ i, LocalMap (T i) (Q i)) :
    LocalMap (Tensor.directSum T) (Tensor.directSum Q) where
  x := fun x s => if x.1 = s.1 then (maps x.1).x x.2 s.2 else 0
  y := fun y s => if y.1 = s.1 then (maps y.1).y y.2 s.2 else 0
  z := fun z s => if z.1 = s.1 then (maps z.1).z z.2 s.2 else 0
  coefficient := by
    have h := Replication.restrict_directSum T
      (fun i => (maps i).x) (fun i => (maps i).y) (fun i => (maps i).z)
    simpa only [fun i => (maps i).coefficient] using h

def selectBranches {I J : Type} [Fintype I] [Fintype J]
    (T : I → Tensor F X Y Z) (select : J → I) (injective : Function.Injective select) :
    LocalMap (Tensor.directSum T) (Tensor.directSum (fun j => T (select j))) where
  x := fun x s => if s = (select x.1, x.2) then 1 else 0
  y := fun y s => if s = (select y.1, y.2) then 1 else 0
  z := fun z s => if s = (select z.1, z.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, injective.eq_iff]

def unflatten (source : Tensor F X Y Z) (R I : Type) [Fintype R] [Fintype I] :
    LocalMap (Tensor.directSum (fun _ : R × I => source))
      (Tensor.directSum (fun _ : R => Tensor.directSum (fun _ : I => source))) where
  x := fun x s => if s = ((x.1, x.2.1), x.2.2) then 1 else 0
  y := fun y s => if s = ((y.1, y.2.1), y.2.2) then 1 else 0
  z := fun z s => if s = ((z.1, z.2.1), z.2.2) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def flatten (source : Tensor F X Y Z) (I J : Type) [Fintype I] [Fintype J] :
    LocalMap (Tensor.directSum (fun _ : I => Tensor.directSum (fun _ : J => source)))
      (Tensor.directSum (fun _ : I × J => source)) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, Tensor.directSum, Prod.ext_iff]
    split_ifs <;> aesop

def replicationProduct {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (finished : Tensor F U V W)
    (R : Type) [Fintype R] :
    LocalMap (Tensor.directSum (fun _ : R => Tensor.product active finished))
      (Tensor.product (Tensor.directSum (fun _ : R => active)) finished) where
  x := fun x s => if s = (x.1.1, (x.1.2, x.2)) then 1 else 0
  y := fun y s => if s = (y.1.1, (y.1.2, y.2)) then 1 else 0
  z := fun z s => if s = (z.1.1, (z.1.2, z.2)) then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp [Tensor.pullback, Tensor.directSum, Tensor.product, ite_mul]

def extract (T : Tensor F X Y Z) {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent T assignment) :
    LocalMap T (Tensor.directSum (JointExtraction.branch T assignment)) where
  x := JointExtraction.assignmentMatrix assignment.x
  y := JointExtraction.assignmentMatrix assignment.y
  z := JointExtraction.assignmentMatrix assignment.z
  coefficient := JointExtraction.restrict_assignments_eq_directSum T assignment coherent

def repairBranches {I : Type} [Fintype I]
    (T Q : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (Q i) (T i) L) :
    LocalMap
      (Tensor.directSum (fun _ : InverseLinearRecovery.MaskRectangles L => Tensor.directSum T))
      (Tensor.directSum Q) := by
  choose a b c h using repair
  exact ofExists (Replication.repair_branches T Q a b c h)

end LocalMap

structure Execution {SX SY SZ X Y Z : Type}
    [Fintype SX] [Fintype SY] [Fintype SZ]
    (source : Tensor F SX SY SZ) (target : Tensor F X Y Z) where
  Copies : Type
  [copies_finite : Fintype Copies]
  copies_positive : 0 < Fintype.card Copies
  map : LocalMap (Tensor.directSum (fun _ : Copies => source)) target

attribute [instance] Execution.copies_finite

namespace Execution

variable {SX SY SZ X Y Z X' Y' Z' : Type}
  [Fintype SX] [Fintype SY] [Fintype SZ]
  [Fintype X] [Fintype Y] [Fintype Z]
  {source : Tensor F SX SY SZ} {current : Tensor F X Y Z}

def initial (source : Tensor F SX SY SZ) : Execution source source where
  Copies := PUnit
  copies_positive := by simp
  map := {
    x := fun x s => if s = (PUnit.unit, x) then 1 else 0
    y := fun y s => if s = (PUnit.unit, y) then 1 else 0
    z := fun z s => if s = (PUnit.unit, z) then 1 else 0
    coefficient := by
      rw [← Tensor.pullback_eq_restrict]
      funext x y z
      simp [Tensor.pullback, Tensor.directSum]
  }

def restrict (E : Execution source current) (target : Tensor F X' Y' Z')
    (map : LocalMap current target) : Execution source target where
  Copies := E.Copies
  copies_positive := E.copies_positive
  map := E.map.comp map

def replicate (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) :
    Execution source (Tensor.directSum (fun _ : R => current)) where
  Copies := R × E.Copies
  copies_positive := by simpa using Nat.mul_pos positive E.copies_positive
  map := ((LocalMap.unflatten source R E.Copies).comp (E.map.parallelCopies R)).withSource _
    (by funext x y z; simp only [Tensor.directSum])

def step (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Execution source target :=
  (E.replicate R positive).restrict target map

def stepOnLeft {U V W : Type} [Fintype U] [Fintype V] [Fintype W]
    (active : Tensor F X Y Z) (finished : Tensor F U V W)
    (E : Execution source (Tensor.product active finished))
    (R : Type) [Fintype R] (positive : 0 < Fintype.card R)
    (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => active)) target) :
    Execution source (Tensor.product target finished) :=
  E.step R positive _ ((LocalMap.replicationProduct active finished R).comp
    (map.product (LocalMap.identity finished)))

def branchOperation {I J R : Type} [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Execution source (Tensor.directSum (fun _ : I × J => next)) :=
  E.step R positive _ ((LocalMap.ofExists
    (Replication.repair_branches (fun _ : I => current)
      (fun _ : I => Tensor.directSum (fun _ : J => next))
      (fun _ => map.x) (fun _ => map.y) (fun _ => map.z)
      (fun _ => map.coefficient))).comp (LocalMap.flatten next I J))

@[simp] theorem branchOperation_copies {I J R : Type}
    [Fintype I] [Fintype J] [Fintype R]
    (current : Tensor F X Y Z) (next : Tensor F X' Y' Z')
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (E : Execution source (Tensor.directSum (fun _ : I => current)))
    (positive : 0 < Fintype.card R)
    (map : LocalMap (Tensor.directSum (fun _ : R => current))
      (Tensor.directSum (fun _ : J => next))) :
    Fintype.card (branchOperation current next E positive map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  exact Fintype.card_prod R E.Copies

@[simp] theorem step_copies (E : Execution source current) (R : Type) [Fintype R]
    (positive : 0 < Fintype.card R) (target : Tensor F X' Y' Z')
    (map : LocalMap (Tensor.directSum (fun _ : R => current)) target) :
    Fintype.card (E.step R positive target map).Copies =
      Fintype.card R * Fintype.card E.Copies := by
  exact Fintype.card_prod R E.Copies

def extractAndRepair (E : Execution source current) {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (ideal : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (ideal i)
      (JointExtraction.branch current assignment i) L) :
    Execution source (Tensor.directSum ideal) := by
  let extracted := E.restrict _ (LocalMap.extract current assignment coherent)
  exact extracted.step (InverseLinearRecovery.MaskRectangles L)
    (by simp [InverseLinearRecovery.MaskRectangles]) _
    ((LocalMap.repairBranches (JointExtraction.branch current assignment) ideal L repair).withSource _
      (by
        funext first second third
        simp only [Tensor.directSum]
        split_ifs <;> rfl))

@[simp] theorem extractAndRepair_copies (E : Execution source current)
    {I : Type} [Fintype I]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (ideal : I → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy (ideal i)
      (JointExtraction.branch current assignment i) L) :
    Fintype.card (E.extractAndRepair assignment coherent ideal L repair).Copies =
      2 ^ (3 * L) * Fintype.card E.Copies := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles L × E.Copies) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

def extractSelectedAndRepair (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Execution source (Tensor.directSum ideal) := by
  let extracted := E.restrict _ (LocalMap.extract current assignment coherent)
  let selected := extracted.restrict _
    (LocalMap.selectBranches (JointExtraction.branch current assignment) select injective)
  exact selected.step (InverseLinearRecovery.MaskRectangles L)
    (by simp [InverseLinearRecovery.MaskRectangles]) _
    ((LocalMap.repairBranches (fun j => JointExtraction.branch current assignment (select j))
      ideal L repair).withSource _
      (by
        funext first second third
        simp only [Tensor.directSum]
        split_ifs <;> rfl))

@[simp] theorem extractSelectedAndRepair_copies (E : Execution source current)
    {I J : Type} [Fintype I] [Fintype J]
    (assignment : JointExtraction.Assignment X Y Z I)
    (coherent : JointExtraction.Coherent current assignment)
    (select : J → I) (injective : Function.Injective select)
    (ideal : J → Tensor F X Y Z) (L : ℕ)
    (repair : ∀ j, InverseLinearRecovery.RecoveredBy (ideal j)
      (JointExtraction.branch current assignment (select j)) L) :
    Fintype.card
      (E.extractSelectedAndRepair assignment coherent select injective ideal L repair).Copies =
      2 ^ (3 * L) * Fintype.card E.Copies := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles L × E.Copies) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles, Fintype.card_fin]

end Execution

section Schedule

variable {SX SY SZ : Type} [Fintype SX] [Fintype SY] [Fintype SZ]
  {X Y Z : ℕ → Type} [∀ n, Fintype (X n)] [∀ n, Fintype (Y n)] [∀ n, Fintype (Z n)]
  (source : Tensor F SX SY SZ) (tensor : ∀ n, Tensor F (X n) (Y n) (Z n))
  (start : Execution source (tensor 0))
  (Copies : ℕ → Type) [∀ n, Fintype (Copies n)]
  (positive : ∀ n, 0 < Fintype.card (Copies n))
  (maps : ∀ n, LocalMap (Tensor.directSum (fun _ : Copies n => tensor n)) (tensor (n + 1)))

def run : (n : ℕ) → Execution source (tensor n)
  | 0 => start
  | n + 1 => (run n).step (Copies n) (positive n) (tensor (n + 1)) (maps n)

theorem run_copies (n : ℕ) :
    Fintype.card (run source tensor start Copies positive maps n).Copies =
      Fintype.card start.Copies * ∏ j ∈ Finset.range n, Fintype.card (Copies j) := by
  induction n with
  | zero =>
      change Fintype.card start.Copies =
        Fintype.card start.Copies * ∏ j ∈ Finset.range 0, Fintype.card (Copies j)
      rw [Finset.prod_range_zero, Nat.mul_one]
  | succ n ih =>
      rw [run, Execution.step_copies, ih, Finset.prod_range_succ]
      ring

end Schedule

section CWSource

variable {K N a b c L : ℕ}

abbrev cwSource (F : Type*) [Field F] (K N : ℕ) :=
  Tensor.power (FieldCW.tensor F 5) (8 * K * N)

def startCW (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (cwSource F K N) :=
  Execution.initial _

def Execution.toWitness
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) : AllFieldWitness F :=
  AllFieldSource.ofRestriction E.map.x E.map.y E.map.z
    (fun x y z => congrFun (congrFun (congrFun E.map.coefficient x) y) z)
    E.copies_positive ha hb hc hL

@[simp] theorem Execution.toWitness_rankBound
    (E : Execution (cwSource F K N) (AllFieldSource.matrixTarget F a b c L))
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hL : 0 < L) :
    (E.toWitness ha hb hc hL).rankBound =
      Fintype.card E.Copies * ((3 * (8 * K * N) + 1) ^ 2 * 7 ^ (8 * K * N)) := rfl

end CWSource

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialSource

open MatrixMultiplication.Foundation AllFieldFiniteFamily CommonDimensions
open scoped BigOperators Classical

abbrev Sites (K N : ℕ) := Fin K × (Fin N × Fin 8)
abbrev Words (K N : ℕ) := Fin K → Fin N → Fin 8 → Fin 7

def sitesEquiv (K N : ℕ) : Sites K N ≃ Fin (8 * K * N) :=
  Fintype.equivOfCardEq (by simp only [Sites, Fintype.card_prod, Fintype.card_fin]; ring)

def flatten (K N : ℕ) (w : Words K N) : AllFieldSource.Word K N :=
  fun i => let p := (sitesEquiv K N).symm i; w p.1 p.2.1 p.2.2

def groupedSource (F : Type*) [Field F] (K N : ℕ) :
    Tensor F (Words K N) (Words K N) (Words K N) :=
  fun x y z => ∏ p : Sites K N,
    FieldCW.tensor F 5 (x p.1 p.2.1 p.2.2) (y p.1 p.2.1 p.2.2) (z p.1 p.2.1 p.2.2)

theorem groupedSource_eq_lots (F : Type*) [Field F] (K N : ℕ) :
    groupedSource F K N =
      familyProduct (fun _ : Fin K => Tensor.power (Tensor.power (FieldCW.tensor F 5) 8) N) := by
  funext x y z
  simp only [groupedSource, Sites, familyProduct, Tensor.power, Fintype.prod_prod_type]

def groupingMap (F : Type*) [Field F] (K N : ℕ) :
    LocalMap (cwSource F K N) (groupedSource F K N) where
  x := fun x s => if s = flatten K N x then 1 else 0
  y := fun y s => if s = flatten K N y then 1 else 0
  z := fun z s => if s = flatten K N z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    simp only [Tensor.pullback, cwSource, Tensor.power, groupedSource, flatten]
    apply Fintype.prod_equiv (sitesEquiv K N).symm
    intro i
    rfl

def initialExecution (F : Type*) [Field F] (K N : ℕ) :
    Execution (cwSource F K N) (groupedSource F K N) :=
  (startCW F K N).restrict _ (groupingMap F K N)

@[simp] theorem initialExecution_copies (F : Type*) [Field F] (K N : ℕ) :
    Fintype.card (initialExecution F K N).Copies = 1 := rfl

end MatrixMultiplication.AllFieldInitialSource

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalInitial

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open InheritedMasks CWStrands
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ)

abbrev Word := Fin 8 → Fin 7
abbrev RawWords := ∀ h, Positions counts h → Word
abbrev CanonicalWords := ∀ c : ClassKey (H := H), ClassPositions counts c → Word

def wholeEquiv (e : Target counts) : RawWords counts ≃ CanonicalWords counts where
  toFun w := fun c j => w c.1 ((positionEquiv counts e c.1).symm ⟨c.2, j⟩)
  invFun w := fun h i => w (h, (e h).val i) (positionEquiv counts e h i).2
  left_inv w := by
    funext h i
    change w h ((positionEquiv counts e h).symm (positionEquiv counts e h i)) = w h i
    simp
  right_inv w := by
    funext c j
    exact congrArg (fun p : Σ u, Fin (counts c.1 u) => w (c.1, p.1) p.2)
      ((positionEquiv counts e c.1).apply_symm_apply ⟨c.2, j⟩)

def rawSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  classProduct (fun _ : H => strand (Fin 8))

def coarseWord (w : RawWords counts) : Position counts → Fin 17 :=
  fun i => CWCoarseIndices.coarseIndex (by simp) (w i.1 i.2)

def ideal (e : Target counts) : Tensor F (RawWords counts) (RawWords counts)
    (RawWords counts) :=
  JointIdealBranches.ideal (rawSource counts) (coarseWord counts) (coarseWord counts)
    (coarseWord counts) (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)
    (triple counts e)

def canonical : Tensor F (CanonicalWords counts) (CanonicalWords counts)
    (CanonicalWords counts) :=
  classProduct (fun c : ClassKey (H := H) => shapeTensor (Fin 8) (shapeNat c.2))

omit [DecidableEq H] in
theorem canonical_pack (e : Target counts) (x y z : RawWords counts) :
    canonical counts (wholeEquiv counts e x) (wholeEquiv counts e y)
      (wholeEquiv counts e z) =
      ∏ h, ∏ i, shapeTensor (F := F) (Fin 8) (shapeNat ((e h).val i))
        (x h i) (y h i) (z h i) := by
  unfold canonical classProduct
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  rw [← Fintype.prod_sigma']
  apply Fintype.prod_equiv (positionEquiv counts e h).symm
  intro i
  simp only [wholeEquiv, Equiv.coe_fn_mk, positionEquiv_symm_shape]

omit [DecidableEq H] in
theorem ideal_eq_canonical (e : Target counts) (x y z : RawWords counts) :
    ideal (F := F) counts e x y z = canonical counts (wholeEquiv counts e x)
      (wholeEquiv counts e y) (wholeEquiv counts e z) := by
  rw [canonical_pack]
  simp only [ideal, JointIdealBranches.ideal, ExactRecovery.delete, and_true,
    rawSource, classProduct, shapeTensor, Fintype.prod_ite_zero, forall_and]
  congr 1
  simp [coarseWord, triple, shapeNat, shapeSide, CWCoarseIndices.coarseIndex,
    funext_iff, Fin.ext_iff, Sigma.forall]

def coordinateMatrix (e : Target counts) : CanonicalWords counts → RawWords counts → F :=
  fun x v => if v = (wholeEquiv counts e).symm x then 1 else 0

theorem ideal_restrict (e : Target counts) :
    Tensor.restrict (coordinateMatrix (F := F) counts e) (coordinateMatrix counts e)
      (coordinateMatrix counts e) (ideal counts e) = canonical counts := by
  funext x y z
  simp only [Tensor.restrict, coordinateMatrix]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  rw [ideal_eq_canonical]
  simp

omit [DecidableEq H] in
theorem coarse_support (x y z : RawWords counts)
    (hT : rawSource (F := F) counts x y z ≠ 0) (i : Position counts) :
    (coarseWord counts x i).val + (coarseWord counts y i).val +
      (coarseWord counts z i).val = 16 := by
  have hh : strand (F := F) (Fin 8) (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) ≠ 0 := by
    intro hz
    apply hT
    unfold rawSource classProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i.1)
    exact Finset.prod_eq_zero (Finset.mem_univ i.2) hz
  simpa [coarseWord] using
    CWCoarseIndices.strand_coarse_support (F := F) (by simp)
      (x i.1 i.2) (y i.1 i.2) (z i.1 i.2) hh

def sideMask (s : Fin 3) (w : RawWords counts) : Prop :=
  ∀ h a, wordPopulation (fun i => coarseWord counts w ⟨h, i⟩) a =
    wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

def maskedSource : Tensor F (RawWords counts) (RawWords counts) (RawWords counts) :=
  ExactRecovery.delete (rawSource counts) (sideMask counts 0) (sideMask counts 1)
    (sideMask counts 2)

omit [Fintype H] [DecidableEq H] in
theorem sideMask_of_target (s : Fin 3) (e : Target counts) (w : RawWords counts)
    (he : coarseWord counts w =
      fun i => sideWord counts s (triple counts e) i.1 i.2) :
    sideMask counts s w := by
  intro h a
  rw [he]
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

theorem maskedSource_support (x y z : RawWords counts)
    (hT : maskedSource (F := F) counts x y z ≠ 0) :
    (coarseWord counts x, coarseWord counts y, coarseWord counts z) ∈
      ambientSet counts (fun _ => 16) := by
  have hm : sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
    by_contra hn
    simp [maskedSource, ExactRecovery.delete, hn] at hT
  have hr : rawSource (F := F) counts x y z ≠ 0 := by
    simpa [maskedSource, ExactRecovery.delete, hm] using hT
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · intro i
    exact coarse_support counts x y z hr i
  · intro h s a
    fin_cases s
    · exact hm.1 h a
    · exact hm.2.1 h a
    · exact hm.2.2 h a

omit [DecidableEq H] in
theorem ideal_support_masks (e : Target counts) (x y z : RawWords counts)
    (hT : ideal (F := F) counts e x y z ≠ 0) :
    sideMask counts 0 x ∧ sideMask counts 1 y ∧ sideMask counts 2 z := by
  have hc : coarseWord counts x = (triple counts e).1 ∧
      coarseWord counts y = (triple counts e).2.1 ∧
      coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn] at hT
  constructor
  · apply sideMask_of_target counts 0 e x
    simpa [sideWord, shapeSide] using hc.1
  constructor
  · apply sideMask_of_target counts 1 e y
    simpa [sideWord, shapeSide] using hc.2.1
  · apply sideMask_of_target counts 2 e z
    simpa [sideWord, shapeSide] using hc.2.2

omit [DecidableEq H] in
theorem delete_ideal_eq (e : Target counts) :
    ExactRecovery.delete (ideal (F := F) counts e) (sideMask counts 0)
      (sideMask counts 1) (sideMask counts 2) = ideal counts e := by
  funext x y z
  by_cases h : ideal (F := F) counts e x y z = 0
  · rw [ExactRecovery.delete, h]
    simp
  · rw [ExactRecovery.delete, ite_eq_left (ideal_support_masks counts e x y z h)]

end MatrixMultiplication.JointCanonicalInitial

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialStep

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialSource
open JointPopulation
open scoped BigOperators Classical

variable {F : Type*} [Field F] {K N : ℕ}
  (counts : Fin K → Shape → ℕ) (total : ∀ h, ∑ u, counts h u = N)

def toLots (w : JointCanonicalInitial.RawWords counts) : Words K N :=
  fun h i => w h ((finCongr (total h)).symm i)

def positionMap :
    LocalMap (groupedSource F K N) (JointCanonicalInitial.rawSource counts) where
  x := fun x s => if s = toLots counts total x then 1 else 0
  y := fun y s => if s = toLots counts total y then 1 else 0
  z := fun z s => if s = toLots counts total z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict, groupedSource_eq_lots]
    funext x y z
    change (∏ h : Fin K, ∏ i : Fin N, CWStrands.strand (F := F) (Fin 8)
      (x h ((finCongr (total h)).symm i))
      (y h ((finCongr (total h)).symm i))
      (z h ((finCongr (total h)).symm i))) =
      ∏ h : Fin K, ∏ i : Positions counts h, CWStrands.strand (F := F) (Fin 8)
        (x h i) (y h i) (z h i)
    apply Finset.prod_congr rfl
    intro h _
    apply Fintype.prod_equiv (finCongr (total h)).symm
    intro i
    rfl

def initialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.rawSource counts) :=
  (AllFieldInitialSource.initialExecution F K N).restrict _ (positionMap counts total)

@[simp] theorem initialExecution_copies :
    Fintype.card (initialExecution (F := F) counts total).Copies = 1 := rfl

def maskedInitialExecution :
    Execution (cwSource F K N) (JointCanonicalInitial.maskedSource counts) :=
  (initialExecution counts total).restrict _
    (LocalMap.delete (JointCanonicalInitial.rawSource counts)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2))

abbrev CoarseWord := Position counts → Fin 17

def ordinaryAssignments (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Assignment (JointCanonicalInitial.RawWords counts)
      (JointCanonicalInitial.RawWords counts) (JointCanonicalInitial.RawWords counts)
      (JointCoarseHashing.Triple (Position counts)) :=
  JointCoarseAssignment.assignments (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True)

theorem ordinaryAssignments_coherent (hx hy hz : CoarseWord counts → Prop) :
    JointExtraction.Coherent (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) := by
  apply JointCoarseAssignment.assignments_coherent
  · exact JointCanonicalInitial.maskedSource_support counts
  · intro _ _ _ _ _ _ _
    trivial
  · intro _ _ _ _ _ _ _ _
    trivial

def initialCanonicalMap (e : Target counts) :
    LocalMap (JointCanonicalInitial.ideal (F := F) counts e)
      (JointCanonicalInitial.canonical counts) where
  x := JointCanonicalInitial.coordinateMatrix counts e
  y := JointCanonicalInitial.coordinateMatrix counts e
  z := JointCanonicalInitial.coordinateMatrix counts e
  coefficient := JointCanonicalInitial.ideal_restrict counts e

def canonicalize {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) :=
  E.restrict _ (LocalMap.directSum _ _ (fun i => initialCanonicalMap counts (target i)))

@[simp] theorem canonicalize_copies {I : Type} [Fintype I] (target : I → Target counts)
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)))) :
    Fintype.card (canonicalize counts target E).Copies = Fintype.card E.Copies := rfl

def repairedInitialExecution {I : Type} [Fintype I]
    (hx hy hz : CoarseWord counts → Prop) (target : I → Target counts)
    (injective : Function.Injective target) (shifts : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy
      (JointCanonicalInitial.ideal (F := F) counts (target i))
      (JointExtraction.branch (JointCanonicalInitial.maskedSource counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))) shifts) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) :=
  canonicalize counts target
    ((maskedInitialExecution counts total).extractSelectedAndRepair
      (ordinaryAssignments counts hx hy hz) (ordinaryAssignments_coherent counts hx hy hz)
      (fun i => triple counts (target i)) ((triple_injective counts).comp injective)
      (fun i => JointCanonicalInitial.ideal counts (target i)) shifts repair)

@[simp] theorem repairedInitialExecution_copies {I : Type} [Fintype I]
    (hx hy hz : CoarseWord counts → Prop) (target : I → Target counts)
    (injective : Function.Injective target) (shifts : ℕ)
    (repair : ∀ i, InverseLinearRecovery.RecoveredBy
      (JointCanonicalInitial.ideal (F := F) counts (target i))
      (JointExtraction.branch (JointCanonicalInitial.maskedSource counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))) shifts) :
    Fintype.card
      (repairedInitialExecution counts total hx hy hz target injective shifts repair).Copies =
      2 ^ (3 * shifts) := by
  change Fintype.card (InverseLinearRecovery.MaskRectangles shifts × PUnit) = _
  rw [Fintype.card_prod, ExactRecovery.card_mask_rectangles,
    Fintype.card_fin, Fintype.card_punit, mul_one]

end MatrixMultiplication.AllFieldInitialStep

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialExact

open MatrixMultiplication.Foundation AllFieldFiniteFamily AllFieldInitialStep
open JointPopulation JointCoarseAssignment JointExtraction JointAssignmentLoss
open scoped BigOperators Classical

attribute [local instance] Classical.propDecidable

private def assignedDeletion {F X Y Z A B C : Type*} [CommSemiring F]
    (T : Tensor F X Y Z) (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop) : Tensor F X Y Z :=
  ExactRecovery.delete T (fun x => a.x x = some e ∧ px x)
    (fun y => a.y y = some e ∧ py y) (fun z => a.z z = some e ∧ pz z)

private theorem assignedDeletion_eq_self_of_support {F X Y Z A B C : Type*}
    [CommSemiring F] (T : Tensor F X Y Z)
    (a : Assignment X Y Z (Triple A B C)) (e : Triple A B C)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    (support : ∀ x y z, T x y z ≠ 0 →
      (a.x x = some e ∧ px x) ∧ (a.y y = some e ∧ py y) ∧ (a.z z = some e ∧ pz z)) :
    assignedDeletion T a e px py pz = T := by
  funext x y z
  unfold assignedDeletion ExactRecovery.delete
  by_cases ht : T x y z = 0
  · simp only [ht, ite_self]
  · exact ite_eq_left (support x y z ht)

variable {K N : ℕ}
  (counts : Fin K → Shape → ℕ)
  (hx hy hz : CoarseWord counts → Prop)

def Isolated (e : Target counts) : Prop :=
  survives hx hy hz (triple counts e) ∧
    ∀ f ∈ ambientSet counts (fun _ => 16), survives hx hy hz f →
      JointCoarseHashing.SharesSide (triple counts e) f → f = triple counts e

section Coefficients

variable {F : Type*} [CommRing F]

theorem assignments_on_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e)
    (x y z : JointCanonicalInitial.RawWords counts)
    (nonzero : JointCanonicalInitial.ideal (F := F) counts e x y z ≠ 0) :
    (ordinaryAssignments counts hx hy hz).x x = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).y y = some (triple counts e) ∧
      (ordinaryAssignments counts hx hy hz).z z = some (triple counts e) := by
  have hc : JointCanonicalInitial.coarseWord counts x = (triple counts e).1 ∧
      JointCanonicalInitial.coarseWord counts y = (triple counts e).2.1 ∧
      JointCanonicalInitial.coarseWord counts z = (triple counts e).2.2 := by
    by_contra hn
    simp [JointCanonicalInitial.ideal, JointIdealBranches.ideal, ExactRecovery.delete, hn]
      at nonzero
  have ht : triple counts e ∈ targetSet counts :=
    Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have he : triple counts e ∈ eligible (ambientSet counts (fun _ => 16))
      (targetSet counts) hx hy hz := by
    apply (mem_eligible_iff _ _ _ _ _ _).2
    exact ⟨ha, ht, isolated.1, fun f hf hs hfx => isolated.2 f hf hs (Or.inl hfx)⟩
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he hc.1 trivial
    intro f hf hfx
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inl (hfx.symm.trans hc.1))
  constructor
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.1, trivial⟩ trivial
    intro f hf hfy
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inl (hfy.1.symm.trans hc.2.1)))
  · apply assignUseful_of_unique _ _ _ _ _ he ⟨hc.2.2, trivial⟩ trivial
    intro f hf hfz
    have hm := (mem_eligible_iff _ _ _ _ _ _).1 hf
    exact isolated.2 f hm.1 hm.2.2.1 (Or.inr (Or.inr (hfz.1.symm.trans hc.2.2)))

private theorem branch_eq_masked_ideal (e : Target counts) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      assignedDeletion (JointCanonicalInitial.ideal counts e)
        (ordinaryAssignments counts hx hy hz) (triple counts e)
        (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
        (JointCanonicalInitial.sideMask counts 2) :=
  JointIdealBranches.branch_masked_eq_delete_ideal
    (JointCanonicalInitial.rawSource (F := F) counts)
    (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
    (JointCanonicalInitial.sideMask counts 2) (ambientSet counts (fun _ => 16)) (targetSet counts)
    hx hy hz (JointCanonicalInitial.coarseWord counts) (JointCanonicalInitial.coarseWord counts)
    (JointCanonicalInitial.coarseWord counts) (fun _ _ => True) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) (triple counts e)

theorem branch_eq_ideal (e : Target counts)
    (ha : triple counts e ∈ ambientSet counts (fun _ => 16))
    (isolated : Isolated counts hx hy hz e) :
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts e) =
      JointCanonicalInitial.ideal counts e := by
  have hdelete : assignedDeletion (JointCanonicalInitial.ideal (F := F) counts e)
      (ordinaryAssignments counts hx hy hz) (triple counts e)
      (JointCanonicalInitial.sideMask counts 0) (JointCanonicalInitial.sideMask counts 1)
      (JointCanonicalInitial.sideMask counts 2) =
      JointCanonicalInitial.ideal counts e := by
    apply assignedDeletion_eq_self_of_support
    intro x y z hh
    have hm := JointCanonicalInitial.ideal_support_masks counts e x y z hh
    have ha := assignments_on_ideal counts hx hy hz e ha isolated x y z hh
    exact ⟨⟨ha.1, hm.1⟩, ⟨ha.2.1, hm.2.1⟩, ⟨ha.2.2, hm.2.2⟩⟩
  exact (branch_eq_masked_ideal counts hx hy hz e).trans hdelete

end Coefficients

section Execution

variable {F : Type*} [Field F]

def selectedExecution (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical counts)) := by
  let input := maskedInitialExecution (F := F) counts total
  let extracted := input.restrict _
    (LocalMap.extract (JointCanonicalInitial.maskedSource counts)
      (ordinaryAssignments counts hx hy hz) (ordinaryAssignments_coherent counts hx hy hz))
  let selected := extracted.restrict _
    (LocalMap.selectBranches
      (branch (JointCanonicalInitial.maskedSource counts) (ordinaryAssignments counts hx hy hz))
      (fun i => triple counts (target i)) ((triple_injective counts).comp injective))
  have heq : Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))) =
      Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i)) := by
    apply congrArg Tensor.directSum
    funext i
    exact branch_eq_ideal counts hx hy hz (target i) (ambient i) (isolated i)
  let idMap := LocalMap.identity (Tensor.directSum (fun i =>
    branch (JointCanonicalInitial.maskedSource (F := F) counts)
      (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
  let sameCoordinates : LocalMap
      (Tensor.directSum (fun i => branch (JointCanonicalInitial.maskedSource (F := F) counts)
        (ordinaryAssignments counts hx hy hz) (triple counts (target i))))
      (Tensor.directSum (fun i => JointCanonicalInitial.ideal counts (target i))) :=
    { x := idMap.x
      y := idMap.y
      z := idMap.z
      coefficient := idMap.coefficient.trans heq }
  exact AllFieldInitialStep.canonicalize counts target (selected.restrict _ sameCoordinates)

@[simp] theorem selectedExecution_copies (total : ∀ h, ∑ u, counts h u = N)
    {I : Type} [Fintype I] (target : I → Target counts)
    (injective : Function.Injective target)
    (ambient : ∀ i, triple counts (target i) ∈ ambientSet counts (fun _ => 16))
    (isolated : ∀ i, Isolated counts hx hy hz (target i)) :
    Fintype.card (selectedExecution (F := F) counts hx hy hz total target
      injective ambient isolated).Copies = 1 := rfl

end Execution

end MatrixMultiplication.AllFieldInitialExact

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialState

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters AllFieldFiniteFamily
open scoped BigOperators Classical

variable {K : ℕ} (allocation : Allocation) (dilation : ℕ)

abbrev CanonicalKey := JointCanonicalization.ClassKey (H := Fin K)

abbrev PlacementPositions (p : InitialPlacement K) :=
  Fin (population allocation dilation (.initial p.1, p.2))

def classPosition (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    Σ p : InitialPlacement K, PlacementPositions allocation dilation p :=
  let q := initialClassPositionEquiv allocation dilation c.1 c.2 i
  ⟨((c.1, q.1.val.1), q.1.val.2), q.2⟩

theorem classPosition_shape (c : CanonicalKey (K := K))
    (i : Fin (initialJointCounts allocation dilation c.1 c.2)) :
    JointCanonicalCW.shapeNat c.2 =
      physicalShape (classPosition allocation dilation c i).1.2
        (initialShape (classPosition allocation dilation c i).1.1) := by
  have h := congrArg decodeShape (initialClassPosition_shape allocation dilation c.1 c.2 i)
  change decodeShape c.2 = _
  simpa only [rootShape, decode_encodePhysicalShape, classPosition] using h.symm

theorem prod_classPosition {F : Type*} [CommMonoid F]
    (f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F) :
    (∏ c : CanonicalKey (K := K),
      ∏ i : Fin (initialJointCounts allocation dilation c.1 c.2),
        f (classPosition allocation dilation c i).1
          (classPosition allocation dilation c i).2) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
  conv_lhs => rw [Fintype.prod_prod_type]
  conv_rhs =>
    rw [Fintype.prod_prod_type]
    rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (∏ u : JointPopulation.Shape, ∏ i : Fin (initialJointCounts allocation dilation j u),
        f (classPosition allocation dilation (j, u) i).1
          (classPosition allocation dilation (j, u) i).2) =
        ∏ u : JointPopulation.Shape, ∏ p : InitialShapeFiber j u,
          ∏ i : Fin (population allocation dilation (.initial (j, p.val.1), p.val.2)),
            f ((j, p.val.1), p.val.2) i := by
      apply Finset.prod_congr rfl
      intro u _
      rw [← Fintype.prod_sigma']
      apply Fintype.prod_equiv (initialClassPositionEquiv allocation dilation j u)
      intro i
      rfl
    _ = ∏ p : Fin sortedInitial.length × Placement,
          ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
            f ((j, p.1), p.2) i :=
      Fintype.prod_fiberwise (fun p : Fin sortedInitial.length × Placement =>
        rootShape (j, p.1) p.2)
        (fun p => ∏ i : Fin (population allocation dilation (.initial (j, p.1), p.2)),
          f ((j, p.1), p.2) i)
    _ = _ := by rw [Fintype.prod_prod_type]

abbrev StateWords := ∀ h : State K 0, HistoryWord allocation dilation h.val

def toCanonical (w : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.CanonicalWords (initialJointCounts (K := K) allocation dilation) :=
  fun c i =>
    let q := classPosition allocation dilation c i
    w ((initialStateEquiv K).symm q.1) q.2

theorem coefficient (F : Type*) [Field F] (ε : ℝ)
    (x y z : StateWords (K := K) allocation dilation) :
    JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
      (toCanonical allocation dilation x) (toCanonical allocation dilation y)
      (toCanonical allocation dilation z) =
      stateTensor F allocation dilation ε 0 x y z := by
  let f : ∀ p : InitialPlacement K, PlacementPositions allocation dilation p → F :=
    fun p i => CWStrands.shapeTensor (Fin 8) (physicalShape p.2 (initialShape p.1))
      (x ((initialStateEquiv K).symm p) i)
      (y ((initialStateEquiv K).symm p) i)
      (z ((initialStateEquiv K).symm p) i)
  have hcanonical :
      JointCanonicalInitial.canonical (F := F) (initialJointCounts allocation dilation)
        (toCanonical allocation dilation x) (toCanonical allocation dilation y)
        (toCanonical allocation dilation z) =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    rw [← prod_classPosition allocation dilation f]
    unfold JointCanonicalInitial.canonical InheritedMasks.classProduct
    apply Finset.prod_congr rfl
    intro c _
    apply Finset.prod_congr rfl
    intro i _
    dsimp only [toCanonical, f]
    rw [classPosition_shape allocation dilation c i]
  have hstate : stateTensor F allocation dilation ε 0 x y z =
      ∏ p : InitialPlacement K, ∏ i : PlacementPositions allocation dilation p, f p i := by
    change (∏ h : State K 0, historyTensor F allocation dilation ε h.val (x h) (y h) (z h)) = _
    rw [← (initialStateEquiv K).symm.prod_comp
      (fun h : State K 0 => historyTensor F allocation dilation ε h.val (x h) (y h) (z h))]
    apply Finset.prod_congr rfl
    intro p _
    change historyTensor F allocation dilation ε (.initial p.1, p.2)
      (x ((initialStateEquiv K).symm p)) (y ((initialStateEquiv K).symm p))
      (z ((initialStateEquiv K).symm p)) = _
    rw [historyTensor_initial]
    rfl
  exact hcanonical.trans hstate.symm

def map (F : Type*) [Field F] (ε : ℝ) :
    LocalMap
      (JointCanonicalInitial.canonical (F := F) (initialJointCounts (K := K) allocation dilation))
      (stateTensor F (K := K) allocation dilation ε 0) where
  x := fun x s => if s = toCanonical allocation dilation x then 1 else 0
  y := fun y s => if s = toCanonical allocation dilation y then 1 else 0
  z := fun z s => if s = toCanonical allocation dilation z then 1 else 0
  coefficient := by
    rw [← Tensor.pullback_eq_restrict]
    funext x y z
    exact coefficient allocation dilation F ε x y z

def execution (F : Type*) [Field F] (ε : ℝ) {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => stateTensor F (K := K) allocation dilation ε 0)) :=
  E.restrict _ ((map (K := K) allocation dilation F ε).parallelCopies I)

@[simp] theorem execution_copies (F : Type*) [Field F] (ε : ℝ)
    {I : Type} [Fintype I] {N : ℕ}
    (E : Execution (cwSource F K N)
      (Tensor.directSum (fun _ : I => JointCanonicalInitial.canonical
        (initialJointCounts (K := K) allocation dilation)))) :
    Fintype.card (execution allocation dilation F ε E).Copies = Fintype.card E.Copies := rfl

end MatrixMultiplication.AllFieldInitialState

end
end

end MatrixAllFields

end OAI
