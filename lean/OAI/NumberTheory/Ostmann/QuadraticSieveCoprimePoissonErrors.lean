import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonLatticeBounds
import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimePoissonTails
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparation

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

noncomputable def largeDivisorError (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (X Y : ℝ) : ℂ :=
  ∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ)),
    (μ d : ℂ) * nonzeroLattice ψ ((d : ℝ) / X)

noncomputable def smallDivisorError (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (X Y : ℝ) : ℂ :=
  ∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Y),
    (μ d : ℂ) * (((X / d : ℝ) : ℂ) * nonzeroLattice (𝓕 ψ) (X / d))

noncomputable def middleDivisorError (ψ : 𝓢(ℝ, ℂ)) (k : ℕ) (X Y Z L : ℝ) : ℂ :=
  ∑ d ∈ k.divisors.filter (fun d : ℕ => Y < (d : ℝ) ∧ (d : ℝ) ≤ Z),
    (μ d : ℂ) * (((X / d : ℝ) : ℂ) * latticeTail (𝓕 ψ) (X / d) L)

theorem norm_sum_moebius_mul_le (s : Finset ℕ) (F : ℕ → ℂ) :
    ‖∑ d ∈ s, (μ d : ℂ) * F d‖ ≤ ∑ d ∈ s, ‖F d‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (norm_moebius_complex_le_one d) (norm_nonneg _)).trans_eq
    (one_mul _)

theorem mul_div_pow_succ (y C : ℝ) (hy : y ≠ 0) (A : ℕ) :
    y * (C / y ^ (A + 1)) = C * (1 / y) ^ A := by
  rw [pow_succ, div_pow, one_pow]
  field_simp

theorem ratio_pow_le_inv_pow {X Y J : ℝ} (hX : 0 < X) (hXY : X ≤ Y)
    (hJ : 0 < J) (hJY : J ≤ Y / X) {A B : ℕ} (hAB : A ≤ B) :
    (X / Y) ^ B ≤ 1 / J ^ A := by
  have hY : 0 < Y := hX.trans_le hXY
  have hratio : X / Y ≤ 1 := (div_le_one hY).mpr hXY
  have hratioJ : X / Y ≤ 1 / J := by
    apply (div_le_div_iff₀ hY hJ).mpr
    have h := (le_div_iff₀ hX).mp hJY
    nlinarith
  calc
    (X / Y) ^ B ≤ (X / Y) ^ A := pow_le_pow_of_le_one (by positivity) hratio hAB
    _ ≤ (1 / J) ^ A := pow_le_pow_left₀ (by positivity) hratioJ A
    _ = _ := by rw [div_pow, one_pow]

theorem large_cutoff_ratio_bound {R L J : ℝ} (hR : 0 < R) (hJ : 0 < J)
    (hJR : J ≤ R) (hL : R ^ 2 ≤ L) (A : ℕ) :
    R ^ (A + 4) / L ^ (A + 2) ≤ 1 / J ^ A := by
  have hLp : 0 < L := (sq_pos_of_pos hR).trans_le hL
  calc
    _ ≤ 1 / R ^ A := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [one_mul]
      calc
        R ^ (A + 4) * R ^ A = (R ^ 2) ^ (A + 2) := by
          rw [← pow_add, ← pow_mul]
          congr 1
          omega
        _ ≤ L ^ (A + 2) := pow_le_pow_left₀ (sq_nonneg _) hL _
    _ ≤ 1 / J ^ A := one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hJ.le hJR A)

theorem largeDivisorError_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X Y J : ℝ),
      0 < X → X ≤ Y → 0 < J → J ≤ Y / X →
      ‖largeDivisorError ψ k X Y‖ ≤ C * X / J ^ A := by
  obtain ⟨C, hC, hb⟩ := nonzeroLattice_bound ψ (A + 2)
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro k X Y J hX hXY hJ hJY
  have hY : 0 < Y := hX.trans_le hXY
  let s := k.divisors.filter (fun d : ℕ => Y < (d : ℝ))
  have hs (d : ℕ) (hd : d ∈ s) : Y < (d : ℝ) := (Finset.mem_filter.mp hd).2
  have ht (d : ℕ) (hd : d ∈ s) : ‖nonzeroLattice ψ ((d : ℝ) / X)‖ ≤
      C * (X / d) ^ (A + 4) := by
    have hdp : 0 < (d : ℝ) := hY.trans (hs d hd)
    have h := hb ((d : ℝ) / X) (div_pos hdp hX)
    simpa only [Nat.add_assoc, Nat.reduceAdd, div_pow, div_eq_mul_inv, mul_inv_rev,
      inv_inv, mul_pow, inv_pow] using h
  calc
    ‖largeDivisorError ψ k X Y‖ ≤ ∑ d ∈ s, ‖nonzeroLattice ψ ((d : ℝ) / X)‖ :=
      norm_sum_moebius_mul_le s _
    _ ≤ ∑ d ∈ s, C * (X / d) ^ (A + 4) := Finset.sum_le_sum ht
    _ = C * (∑ d ∈ s, (X / d) ^ (A + 4)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (2 * X * (X / Y) ^ (A + 3)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      simpa only [Nat.add_assoc, Nat.reduceAdd] using
        finite_nat_scaled_inverse_pow_tail_le s hX hY hs (A + 2)
    _ ≤ (2 * C) * X / J ^ A := by
      have h := ratio_pow_le_inv_pow hX hXY hJ hJY (A := A) (B := A + 3) (by omega)
      have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * C * X by positivity)
      convert hm using 1 <;> ring

theorem cutoff_power_identity (X Y : ℝ) (hX : X ≠ 0) (A : ℕ) :
    Y * (Y / X) ^ A = X * (Y / X) ^ (A + 1) := by
  rw [pow_succ]
  field_simp

theorem smallDivisorError_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X Y J : ℝ),
      0 < Y → Y ≤ X → 0 < J → J ≤ X / Y →
      ‖smallDivisorError ψ k X Y‖ ≤ C * X / J ^ A := by
  obtain ⟨C, hC, hb⟩ := nonzeroLattice_bound (𝓕 ψ) (A + 2)
  refine ⟨C, hC, ?_⟩
  intro k X Y J hY hYX hJ hJX
  have hX : 0 < X := hY.trans_le hYX
  let s := k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Y)
  have hs (d : ℕ) (hd : d ∈ s) : 0 < d ∧ (d : ℝ) ≤ Y :=
    ⟨Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩
  have ht (d : ℕ) (hd : d ∈ s) :
      ‖((X / d : ℝ) : ℂ) * nonzeroLattice (𝓕 ψ) (X / d)‖ ≤ C * ((d : ℝ) / X) ^ (A + 3) := by
    have hdp : 0 < (d : ℝ) := by exact_mod_cast (hs d hd).1
    have hy : 0 < X / d := div_pos hX hdp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    have h := hb (X / d) hy
    simp only [Nat.add_assoc, Nat.reduceAdd] at h
    apply (mul_le_mul_of_nonneg_left h hy.le).trans_eq
    simpa only [Nat.add_assoc, Nat.reduceAdd, one_div_div] using
      mul_div_pow_succ (X / d) C hy.ne' (A + 3)
  calc
    ‖smallDivisorError ψ k X Y‖ ≤
        ∑ d ∈ s, ‖((X / d : ℝ) : ℂ) * nonzeroLattice (𝓕 ψ) (X / d)‖ :=
      norm_sum_moebius_mul_le s _
    _ ≤ ∑ d ∈ s, C * ((d : ℝ) / X) ^ (A + 3) := Finset.sum_le_sum ht
    _ = C * (∑ d ∈ s, ((d : ℝ) / X) ^ (A + 3)) := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (Y * (Y / X) ^ (A + 3)) :=
      mul_le_mul_of_nonneg_left (finite_nat_scaled_pow_sum_le s hX hY.le hs (A + 3)) hC.le
    _ = C * X * (Y / X) ^ (A + 4) := by
      rw [cutoff_power_identity X Y hX.ne' (A + 3)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      ring
    _ ≤ C * X / J ^ A := by
      have h := ratio_pow_le_inv_pow hY hYX hJ hJX (A := A) (B := A + 4) (by omega)
      have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ C * X by positivity)
      convert hm using 1
      ring

theorem middleDivisorError_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X Y Z J L : ℝ),
      0 < X → X ≤ Z → 0 < J → J ≤ Z / X → (Z / X) ^ 2 ≤ L →
      ‖middleDivisorError ψ k X Y Z L‖ ≤ C * X / J ^ A := by
  obtain ⟨C, hC, hb⟩ := latticeTail_bound (𝓕 ψ) (A + 2)
  refine ⟨C, hC, ?_⟩
  intro k X Y Z J L hX hXZ hJ hJZ hL
  have hZ : 0 < Z := hX.trans_le hXZ
  have hLp : 0 < L := (sq_pos_of_pos (div_pos hZ hX)).trans_le hL
  let s := k.divisors.filter (fun d : ℕ => Y < (d : ℝ) ∧ (d : ℝ) ≤ Z)
  have hs (d : ℕ) (hd : d ∈ s) : 0 < d ∧ (d : ℝ) ≤ Z :=
    ⟨Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2.2⟩
  have ht (d : ℕ) (hd : d ∈ s) :
      ‖((X / d : ℝ) : ℂ) * latticeTail (𝓕 ψ) (X / d) L‖ ≤
        (C / L ^ (A + 2)) * ((d : ℝ) / X) ^ (A + 3) := by
    have hdp : 0 < (d : ℝ) := by exact_mod_cast (hs d hd).1
    have hy : 0 < X / d := div_pos hX hdp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
    have h := hb (X / d) L hy hLp
    simp only [Nat.add_assoc, Nat.reduceAdd] at h
    apply (mul_le_mul_of_nonneg_left h hy.le).trans_eq
    calc
      _ = (X / d) * ((C / L ^ (A + 2)) / (X / d) ^ ((A + 3) + 1)) := by
        simp only [Nat.add_assoc, Nat.reduceAdd, div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        simpa only [one_div_div] using
          mul_div_pow_succ (X / d) (C / L ^ (A + 2)) hy.ne' (A + 3)
  calc
    ‖middleDivisorError ψ k X Y Z L‖ ≤
        ∑ d ∈ s, ‖((X / d : ℝ) : ℂ) * latticeTail (𝓕 ψ) (X / d) L‖ :=
      norm_sum_moebius_mul_le s _
    _ ≤ ∑ d ∈ s, (C / L ^ (A + 2)) * ((d : ℝ) / X) ^ (A + 3) := Finset.sum_le_sum ht
    _ = (C / L ^ (A + 2)) * (∑ d ∈ s, ((d : ℝ) / X) ^ (A + 3)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C / L ^ (A + 2)) * (Z * (Z / X) ^ (A + 3)) :=
      mul_le_mul_of_nonneg_left (finite_nat_scaled_pow_sum_le s hX hZ.le hs (A + 3)) (by positivity)
    _ = C * X * ((Z / X) ^ (A + 4) / L ^ (A + 2)) := by
      rw [cutoff_power_identity X Z hX.ne' (A + 3)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      ring
    _ ≤ C * X / J ^ A := by
      have h := large_cutoff_ratio_bound (div_pos hZ hX) hJ hJZ hL A
      have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ C * X by positivity)
      convert hm using 1
      ring

end Ostmann.QuadraticSieve

end OAI
