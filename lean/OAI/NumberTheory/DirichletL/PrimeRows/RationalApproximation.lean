import OAI.NumberTheory.DirichletL.Poisson.OscillatoryGaussian

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic

open Filter

namespace RationalQuant

private theorem cpos : 0 < Real.log 2 / 20 := by
  have h : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem eventual_log_absorption (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → 2 ≤ D →
      D ^ ((4 / 45 : ℝ) - ε) ≤
        (Real.log 2 / 20) *
          (D ^ (4 / 45 : ℝ) / Real.log (D ^ (4 / 45 : ℝ))) := by
  have hsmall := (isLittleO_log_rpow_atTop hε).bound cpos
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hsmall
  refine ⟨D₀, ?_⟩
  intro D hD hDtwo
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos (by linarith)
  have hpowpos : 0 < D ^ (4 / 45 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hlogYpos : 0 < Real.log (D ^ (4 / 45 : ℝ)) := by
    rw [Real.log_rpow hDpos]
    positivity
  have hlogD : Real.log D ≤
      (Real.log 2 / 20) * D ^ ε := by
    have h := hD₀ D hD
    simpa only [Real.norm_eq_abs, abs_of_pos hlogDpos,
      abs_of_pos (Real.rpow_pos_of_pos hDpos ε)] using h
  have hYleD : D ^ (4 / 45 : ℝ) ≤ D := by
    calc
      D ^ (4 / 45 : ℝ) ≤ D ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
      _ = D := by simp
  have hlogY : Real.log (D ^ (4 / 45 : ℝ)) ≤
      (Real.log 2 / 20) * D ^ ε :=
    (Real.log_le_log hpowpos hYleD).trans hlogD
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlogYpos).mpr
  calc
    D ^ ((4 / 45 : ℝ) - ε) * Real.log (D ^ (4 / 45 : ℝ)) ≤
        D ^ ((4 / 45 : ℝ) - ε) *
          ((Real.log 2 / 20) * D ^ ε) :=
          mul_le_mul_of_nonneg_left hlogY (Real.rpow_nonneg hDpos.le _)
    _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
      calc
        D ^ ((4 / 45 : ℝ) - ε) *
            ((Real.log 2 / 20) * D ^ ε) =
            (Real.log 2 / 20) *
              (D ^ ((4 / 45 : ℝ) - ε) * D ^ ε) := by ring
        _ = (Real.log 2 / 20) *
            D ^ (((4 / 45 : ℝ) - ε) + ε) := by
              rw [← Real.rpow_add hDpos]
        _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
              congr 1
              ring_nf

theorem scale_large_eventually (Y₀ : ℝ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      2 ≤ D ∧ Y₀ ≤ D ^ (4 / 45 : ℝ) := by
  let M : ℝ := max 1 Y₀
  refine ⟨max 2 (M ^ (45 / 4 : ℝ)), ?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left _ _)
  have hpowle : M ^ (45 / 4 : ℝ) ≤ D :=
    (le_max_right _ _).trans hD
  have hroot : M ≤ D ^ (4 / 45 : ℝ) := by
    calc
      M = (M ^ (45 / 4 : ℝ)) ^ (4 / 45 : ℝ) := by
        rw [← Real.rpow_mul hMpos.le]
        have hmul : (45 / 4 : ℝ) * (4 / 45 : ℝ) = 1 := by norm_num
        rw [hmul]
        simp
      _ ≤ D ^ (4 / 45 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hMpos.le _) hpowle (by norm_num)
  exact ⟨hD2, (le_max_right _ _).trans hroot⟩

theorem from_rational_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((4 / 45 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((31 / 15 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (82 / 45 : ℝ)) :
    A ≤ 2 * C * D ^ ((89 / 90 : ℝ) + ε) := by
  let E : ℝ := (89 / 90 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((31 / 15 : ℝ) + ε) ≤
        J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      D ^ ((31 / 15 : ℝ) + ε) =
          D ^ ((4 / 45 : ℝ) - ε) *
            D ^ ((89 / 45 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (82 / 45 : ℝ) ≤
      D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((31 / 15 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (82 / 45 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((89 / 45 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (89 / 45 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((89 / 45 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

theorem rational_row_error_power
    (D r : ℕ) (hD : 1 ≤ D)
    (hrlo : (D : ℝ) ^ (4 / 45 : ℝ) / 3 < (r : ℝ)) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  let X : ℝ := (D : ℝ) ^ (4 / 45 : ℝ)
  let P : ℝ := (D : ℝ) ^ (41 / 45 : ℝ)
  let q : ℝ := (D / r : ℕ)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hXpos : 0 < X := Real.rpow_pos_of_pos hDpos _
  have hqnonneg : 0 ≤ q := by positivity
  have hP1 : 1 ≤ P := by
    calc
      1 = (D : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (D : ℝ) ^ (41 / 45 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDreal (by norm_num)
  have hDP : (D : ℝ) = X * P := by
    dsimp [X, P]
    rw [← Real.rpow_add hDpos]
    norm_num
  have hdivnat : D / r * r ≤ D := Nat.div_mul_le_self D r
  have hdivreal : q * (r : ℝ) ≤ (D : ℝ) := by
    change ((D / r : ℕ) : ℝ) * (r : ℝ) ≤ (D : ℝ)
    exact_mod_cast hdivnat
  have hXr : X ≤ 3 * (r : ℝ) := by
    dsimp [X] at hrlo ⊢
    linarith
  have hXq : X * q ≤ 3 * (D : ℝ) := by
    calc
      X * q ≤ (3 * (r : ℝ)) * q :=
        mul_le_mul_of_nonneg_right hXr hqnonneg
      _ ≤ 3 * (D : ℝ) := by nlinarith [hdivreal]
  have hq : q ≤ 3 * P := by
    apply le_of_mul_le_mul_left (a := X) ?_ hXpos
    calc
      X * q ≤ 3 * (D : ℝ) := hXq
      _ = X * (3 * P) := by rw [hDP]; ring
  have hfinal : (128 : ℝ) * (q + 1) ≤ 512 * P := by
    nlinarith [hq, hP1]
  simpa [q, P] using hfinal

end RationalQuant

open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_count_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      2 ≤ D ∧
      (D : ℝ) ^ ((4 / 45 : ℝ) - ε) ≤
        ((selected ((D : ℝ) ^ (4 / 45 : ℝ))).card : ℝ) := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  obtain ⟨Dlog, hlog⟩ := RationalQuant.eventual_log_absorption ε hε
  obtain ⟨Dscale, hscale⟩ := RationalQuant.scale_large_eventually Y₀
  refine ⟨max Dlog Dscale, ?_⟩
  intro D hD
  have hDl : Dlog ≤ (D : ℝ) := (le_max_left _ _).trans hD
  have hDs : Dscale ≤ (D : ℝ) := (le_max_right _ _).trans hD
  obtain ⟨hDtwo, hY⟩ := hscale (D : ℝ) hDs
  have hDtwoNat : 2 ≤ D := by exact_mod_cast hDtwo
  have habs := hlog (D : ℝ) hDl hDtwo
  have hprime := hcount ((D : ℝ) ^ (4 / 45 : ℝ)) hY
  exact ⟨hDtwoNat, habs.trans (by simpa only [selected] using hprime)⟩

theorem selected_rows_in_ball [DecidableEq O] (D : ℕ) (hD : 1 ≤ D) :
    (selected ((D : ℝ) ^ (4 / 45 : ℝ))).image
      (fun r : ℕ => (r : O) ^ 6) ⊆
      rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ := by
  classical
  intro u hu
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
  have hrI : r ∈ Finset.Ioc
      ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊
      ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_filter.mp hr).1
  have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
  have hrupper : r ≤ ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_Ioc.mp hrI).2
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    Real.rpow_nonneg hDpos.le _
  have hrupperCast : (r : ℝ) ≤
      (⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hrupper
  have hrupperReal : (r : ℝ) ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    hrupperCast.trans (Nat.floor_le hYpos)
  have hnorm : qNat ((r : O) ^ 6) = r ^ 12 := by
    rw [rational_qNat_pow r 6 hrprime.ne_zero]
    ring
  have hpow : (r : ℝ) ^ 12 ≤
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 := by gcongr
  have hYpow : ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
      (D : ℝ) ^ (16 / 15 : ℝ) := by
    calc
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
          (D : ℝ) ^ ((4 / 45 : ℝ) * (12 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 12).symm
      _ = (D : ℝ) ^ (16 / 15 : ℝ) := by congr 1; norm_num
  have hnormreal : (qNat ((r : O) ^ 6) : ℝ) ≤
      (⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ : ℝ) := by
    rw [hnorm]
    exact (by exact_mod_cast hpow :
      ((r ^ 12 : ℕ) : ℝ) ≤ ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12).trans
        (hYpow.le.trans (Nat.le_ceil _))
  exact mem_rowNormBall_of_qNat_le _ _ (by exact_mod_cast hnormreal)

theorem selected_row_error_bound (D : ℕ) (hD : 1 ≤ D)
    (r : ℕ) (hr : r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ))) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  have hrlo : ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊ < r :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  exact RationalQuant.rational_row_error_power D r hD
    (Nat.lt_of_floor_lt hrlo)

end RationalPrimeExtraction

open ActualEisensteinCubic ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_finite_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ A : O → ℂ,
      (∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
        ‖A 1 - A ((r : O) ^ 6)‖ ≤
          512 * (D : ℝ) ^ (41 / 45 : ℝ)) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤
          (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖A 1‖ ≤ 1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₀, hcount⟩ := eventual_count_power ε hε
  refine ⟨D₀, ?_⟩
  intro D hD A happrox hmean
  classical
  obtain ⟨hDtwo, hJcount⟩ := hcount D hD
  have hDone : 1 ≤ D := by omega
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hDone
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  let S := selected ((D : ℝ) ^ (4 / 45 : ℝ))
  let rows := rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊
  let E : ℝ := 512 * (D : ℝ) ^ (41 / 45 : ℝ)
  let M : ℝ := (D : ℝ) ^ ((31 / 15 : ℝ) + ε)
  have hrows : S.image (fun r : ℕ => (r : O) ^ 6) ⊆ rows :=
    selected_rows_in_ball D hDone
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6) (S : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hextract := ShortDraft.complex_row_extraction rows S
    (fun r : ℕ => (r : O) ^ 6) A 1 E M
    (by dsimp [E]; positivity) hrows hinj happrox hmean
  have herr : E ^ 2 = 512 ^ 2 * (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [E]
    rw [mul_pow]
    congr 1
    calc
      ((D : ℝ) ^ (41 / 45 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((41 / 45 : ℝ) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (82 / 45 : ℝ) := by congr 1; norm_num
  rw [herr] at hextract
  have hextract' : (S.card : ℝ) * ‖A 1‖ ^ 2 ≤
      2 * (D : ℝ) ^ ((31 / 15 : ℝ) + ε) +
      2 * (S.card : ℝ) * 512 ^ 2 *
        (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [M] at hextract
    nlinarith [hextract]
  have hbound := RationalQuant.from_rational_prime_rows_with_constant
    (D : ℝ) ε (S.card : ℝ) ‖A 1‖ 512 hDreal hε.le
    (norm_nonneg _) (by norm_num) hJcount hextract'
  simpa only [show (2 : ℝ) * 512 = 1024 by norm_num] using hbound

open ActualEisensteinCubic ShortDraftLatticeCount

theorem actual_rational_prime_extraction
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      (∀ n ∈ columns, qNat n ≤ D) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖∑ n ∈ columns, weight n‖ ≤
        1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₁, hgeneric⟩ := eventual_finite_extraction ε hε
  refine ⟨max 2 D₁, ?_⟩
  intro D hD hcolnorm hmean
  classical
  have hDtwoReal : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD
  have hDtwo : 2 ≤ D := by exact_mod_cast hDtwoReal
  have hDone : 1 ≤ D := by omega
  have hDgeneric : D₁ ≤ (D : ℝ) := (le_max_right _ _).trans hD
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have happrox : ∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
      ‖A 1 - A ((r : O) ^ 6)‖ ≤
        512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
    intro r hr
    have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤ _
    exact (rational_prime_sixth_row_approx P hgood columns support weight
      r hrprime D hsupport hcolnorm hweight).trans
      (selected_row_error_bound D hDone r hr)
  have hmean' :
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤ (D : ℝ) ^ ((31 / 15 : ℝ) + ε) := hmean
  have hbound := hgeneric D hDgeneric A happrox hmean'
  simpa only [hone] using hbound

end RationalPrimeExtraction

namespace OscSpecial

noncomputable def phaseBoundConstant (a b : ℝ) : ℝ :=
  2 * (|a - b| + |a| + |b|) + 1

theorem phaseBoundConstant_pos (a b : ℝ) :
    0 < phaseBoundConstant a b := by
  unfold phaseBoundConstant
  positivity

theorem quadratic_phase_abs_le (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith [htri, h1, h2, h3, hQ]

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

theorem scaled_moment_vanishes_const (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem breveE_period_div_lam_O (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam) = 1 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz, eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates a b

noncomputable def fixedDualPhase (c y : O) : ℂ :=
  ShortDraftTrace.breveE (eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ))

theorem fixedDualPhase_period_two (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  let d : O := -(c * (y*w+w^2))
  have hO : -(c * (y + 2*w)^2) = -(c*y^2) + 4*d := by
    dsimp [d]
    ring
  have h4 : eisEmbedding (4*d) = 4 * eisEmbedding d := by
    simp only [map_mul, map_ofNat]
  have harg :
      eisEmbedding (-(c * (y + 2*w)^2)) / eisLam / (4 : ℂ) =
        eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ) +
          eisEmbedding d / eisLam := by
    rw [hO, map_add, h4]
    ring
  unfold fixedDualPhase
  rw [harg, AddChar.map_add_eq_mul, breveE_period_div_lam_O, mul_one]

theorem fixedDualPhase_eq_of_mod_two (c y z : O)
    (h : Ideal.Quotient.mk (Ideal.span {(2 : O)}) y =
      Ideal.Quotient.mk (Ideal.span {(2 : O)}) z) :
    fixedDualPhase c y = fixedDualPhase c z := by
  have hsub : y-z ∈ Ideal.span {(2 : O)} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hsub
  have hy : y = z + 2*w := by
    calc
      y = z+(y-z) := by ring
      _ = z+2*w := by rw [hw]
  rw [hy, fixedDualPhase_period_two]

theorem fixedDualPhase_weighted_partition (c : O) (W : O → ℂ)
    (hsum : Summable (fun y : O => fixedDualPhase c y * W y)) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑' y : O, fixedDualPhase c y * W y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
          ∑' w : O,
            W (GaussianShiftedPartition.representative 2 r + 2*w) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_by_finite_fibers
    (Ideal.Quotient.mk (Ideal.span {(2 : O)})) _ hsum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {(2 : O)})) ⁻¹' {r}),
      fixedDualPhase c z.1 * W z.1) =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r + 2*w) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) :=
      GaussianFiberEquiv.fiber_tsum 2 h2 r
        (GaussianShiftedPartition.representative 2 r)
        (GaussianShiftedPartition.representative_spec 2 r)
        (fun y => fixedDualPhase c y * W y)
    _ =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) := by
      apply tsum_congr
      intro w
      rw [fixedDualPhase_period_two]
    _ = _ := tsum_mul_left

end ActualEisensteinCubic

namespace OscSpecial

open scoped Topology
open Filter

noncomputable def dualScale (η a b : ℝ) : ℝ :=
  η * q a b / (4 * r η a b)

theorem dualScale_tendsto (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)

theorem abel_mass_dual_scale (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)

end OscSpecial

end

end OAI
