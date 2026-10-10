import OAI.NumberTheory.DirichletL.Descent.IdealMasks
import OAI.NumberTheory.DirichletL.Descent.Fibers
import OAI.NumberTheory.DirichletL.CubicSieve.Ideal

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

local notation "Eis" => ActualEisensteinCubic.O

def inverseCubicKernel (P n : Ideal Eis) : ℂ :=
  star (ConcreteTraceCRT.eisEmbedding
    (CubicJacobiGlobal.idealSymbol P (CompletedGauss.primaryGenerator n)))

theorem inverseCubicKernel_eq_inverse_square (P n : Ideal Eis) :
    inverseCubicKernel P n =
      (CanonicalRowCompletion.idealRowHom (CompletedGauss.primaryGenerator n) P)⁻¹ ^ 2 := by
  rw [inv_pow, CanonicalRowCompletion.idealRowHom_square,
    inverse_eq_square_of_fourth_eq (CubicSieve.idealSymbol_fourth P _)]
  exact (CubicSieve.idealKernel_square_eq_star P n).symm

theorem inverseCubicKernel_norm_le_one (P n : Ideal Eis) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star, CubicSieve.idealKernel] using
    CubicSieve.idealKernel_norm_le_one P n

def hybridCubicCoefficient (R r h t : Ideal Eis) (a : Ideal Eis → ℂ)
    (P : Ideal Eis) : ℂ :=
  (a (R * P) * inverseCubicKernel P r * (if IsCoprime P (h * t) then 1 else 0)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤ 256 := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal Eis) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ 128 * (2 * L) := by
    apply DescentFiberCost.finite_ideal_count_real S (2 * L) (by linarith)
    · intro P hP hz
      have hn := hP0 P hP
      simp [hz] at hn
    · intro P hP
      exact (hS P hP).2
  have hterm (P : Ideal Eis) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (128 * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 256 := by field_simp; ring

theorem hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, ite_eq_left, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (inverseCubicKernel_norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem inverseCubicKernel_mul_left (R P n : Ideal Eis) :
    inverseCubicKernel (R * P) n = inverseCubicKernel R n * inverseCubicKernel P n := by
  simp only [inverseCubicKernel, CubicJacobiGlobal.idealSymbol_mul, map_mul, star_mul]
  ring

theorem inverseCubicKernel_mul_right (P n m : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  rw [map_mul, star_mul]
  ring

theorem inverseCubicKernel_quotients (R P' r c' m : Ideal Eis)
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    inverseCubicKernel (R * P') ((r * c') * m) =
      inverseCubicKernel R ((r * c') * m) * inverseCubicKernel P' r *
        inverseCubicKernel P' (c' * m) := by
  rw [inverseCubicKernel_mul_left, mul_assoc r c' m,
    inverseCubicKernel_mul_right P' r (c' * m) hP']
  ring

theorem inverseCubicKernel_eq_zero_of_not_coprime (P n : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hn : CompletedGauss.primaryGenerator n ≠ 0) (hcop : ¬ IsCoprime P n) :
    inverseCubicKernel P n = 0 := by
  have hc := CubicSieve.idealSymbol_cube_mask P (CompletedGauss.primaryGenerator n) hP
  rw [(CompletedGauss.primaryGenerator_spec n hn).1, ite_eq_right hcop] at hc
  have hz := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hc
  simp only [inverseCubicKernel, hz, star_zero]

theorem hybrid_cubic_column_mask
    (P n b c m h t : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) =
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [inverseCubicKernel_eq_zero_of_not_coprime P n hP hngen hPn]
    simp

theorem hybrid_original_kernel_decomposition
    (k P n b c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) *
      inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
        (inverseCubicKernel P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hybrid_quadratic_square_mask k n b c m h t hk hn hb hct]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients (R r k' P' c' m h : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel (R * P') ((r * c') * m) =
    (CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel R ((r * c') * m)) *
      inverseCubicKernel P' r *
      CanonicalQuadraticSieve.quadraticRow k'
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P' (c' * m) := by
  rw [CanonicalQuadraticSieve.quadraticRow_mul (R * r) k' hk,
    inverseCubicKernel_quotients R P' r c' m hP']
  ring

def hybridColumnCoefficient (R r : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  beta (r * c) m h *
    CanonicalQuadraticSieve.quadraticRow (R * r) (CompletedGauss.primaryGenerator (m * h)) *
    inverseCubicKernel R ((r * c) * m)

theorem hybridColumnCoefficient_norm_le_one (R r c m h : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ *
      ‖CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h))‖ ≤ 1 := by
    exact (mul_le_mul hb (CanonicalQuadraticSieve.quadraticRow_norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (inverseCubicKernel_norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem normalized_ideal_product_weight (R P : Ideal Eis) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hybrid_extracted_block_identity
    (R r k' P' c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
          (CompletedGauss.primaryGenerator (m * h)) *
        inverseCubicKernel (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient R r beta c m h *
      CanonicalQuadraticSieve.quadraticRow k' (CompletedGauss.primaryGenerator (m * h)) *
      hybridCubicCoefficient R r h t a P' * inverseCubicKernel P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

def hybridInner (nset bset : Finset (Ideal Eis))
    (beta : Ideal Eis → Ideal Eis → ℂ) (k P : Ideal Eis) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * CanonicalQuadraticSieve.quadraticRow k
      (CompletedGauss.primaryGenerator (n * b)) * inverseCubicKernel P n *
        (if IsCoprime P b then 1 else 0)

def hybridRow (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner nset bset beta k P

def hybridDivisorTerm (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k R : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, if R ∣ P then
    a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * hybridInner nset bset beta k P else 0

theorem hybridRow_mobius (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k : Ideal Eis) (hk : k ≠ 0) :
    hybridRow Pset nset bset a beta k =
      ∑ R ∈ idealDivisors k, (moebius R : ℂ) *
        ∑ P ∈ Pset, if R ∣ P then
          a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
            hybridInner nset bset beta k P else 0 := by
  unfold hybridRow
  conv_lhs => simp only [ideal_coprime_mobius k _ hk, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hRP : R ∣ P <;> simp only [hRP, ite_true, ite_false, mul_zero, zero_mul]
  ring

theorem hybrid_first_mask_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 1 ≤ K →
      ∀ (rows Pset nset bset : Finset (Ideal Eis))
        (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ R ∈ rows.biUnion idealDivisors, ∑ k ∈ rows,
            if R ∈ idealDivisors k then
              ‖hybridDivisorTerm Pset nset bset a beta k R‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro K hK rows Pset nset bset a beta hrows
  have hrewrite : (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) =
      ∑ k ∈ rows, ‖∑ R ∈ idealDivisors k,
        (moebius R : ℂ) * hybridDivisorTerm Pset nset bset a beta k R‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hybridRow_mobius Pset nset bset a beta k (hrows k hk).1]
    rfl
  rw [hrewrite]
  apply finite_expansion_energy rows (rows.biUnion idealDivisors) idealDivisors
    (fun _ R => (moebius R : ℂ)) (hybridDivisorTerm Pset nset bset a beta) (C * K ^ ε)
  · intro k hk R hR
    exact Finset.mem_biUnion.mpr ⟨k, hk, hR⟩
  · intro k hk R hR
    exact QuadraticInitialBound.norm_ideal_moebius_le_one R
  · intro k hk
    exact (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 hε.le) hC.le)

def doubleMaskRow (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ p ∈ pairs, (if IsCoprime k (p.1 * p.2) then 1 else 0) * F k p.1 p.2

def doubleMaskDivisorTerm (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis)
    (D : Ideal Eis × Ideal Eis) : ℂ :=
  ∑ p ∈ pairs, if D.1 ∣ p.1 ∧ D.2 ∣ p.2 then F k p.1 p.2 else 0

theorem doubleMaskRow_mobius (pairs : Finset (Ideal Eis × Ideal Eis))
    (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) (hk : k ≠ 0) :
    doubleMaskRow pairs F k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) * doubleMaskDivisorTerm pairs F k D := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold doubleMaskRow
  conv_lhs => simp only [hm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [doubleMaskDivisorTerm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : D.1 ∣ p.1 ∧ D.2 ∣ p.2 <;> simp [h]

theorem hybrid_double_mask_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (pairs : Finset (Ideal Eis × Ideal Eis))
      (F : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖doubleMaskRow pairs F k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖doubleMaskDivisorTerm pairs F k D‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows pairs F hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) := doubleMaskRow_mobius pairs F k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (doubleMaskDivisorTerm pairs F) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end

end SevenEighths.InverseMoment

end OAI
