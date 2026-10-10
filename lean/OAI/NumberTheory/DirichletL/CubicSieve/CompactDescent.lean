import OAI.NumberTheory.DirichletL.CubicSieve.Smoothed
import OAI.NumberTheory.DirichletL.CubicSieve.DescentEnergy

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve IdealMobiusDivisorSum SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma majorant_radial_summable (P : O → ℂ) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖^2 / M) * P z) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall M) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside M hM z hz, zero_mul]

lemma majorant_rescale (d z : O) (_hd : d ≠ 0) (M : ℝ) :
    rowMajorant (‖eisEmbedding (d*z)‖^2 / M) =
      rowMajorant (‖eisEmbedding z‖^2 / (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) := by
  rw [map_mul, norm_mul, mul_pow, eisEmbedding_norm_sq_eq_absNorm_span d]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

lemma dividedMajorant_tsum (P : O → ℂ) (d : O) (hd : d ≠ 0)
    (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ dividedRows (rowMajorantBall M) d,
      rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      ∑' z : O, rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z := by
  symm
  rw [← show (fun z : O => rowMajorant (‖eisEmbedding (d*z)‖^2 / M) * P z) =
      (fun z : O => rowMajorant (‖eisEmbedding z‖^2 /
        (M / (Ideal.absNorm (Ideal.span {d}) : ℝ))) * P z) by
          funext z; rw [majorant_rescale d z hd M]]
  apply tsum_eq_sum
  intro z hz
  have hout : d*z ∉ rowMajorantBall M := by
    intro hin
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨d*z, Finset.mem_filter.mpr ⟨hin, dvd_mul_right d z⟩, ?_⟩
    apply mul_left_cancel₀ hd
    exact elementQuotient_mul d (d*z) (dvd_mul_right d z)
  rw [rowMajorant_zero_outside M hM (d*z) hout, zero_mul]

lemma majorant_coprime_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) =
      cubicSmoothedCoprime cols a rowMajorant M := by
  have hs (j k : n) := majorant_radial_summable
    (fun z => if IsCoprime (cols j) (cols k) then
      star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0) M hM
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => hs j k))]
  unfold cubicSmoothedCoprime
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => hs j k)]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro z
    simp only [star_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero, tsum_zero]

lemma compact_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (M : ℝ) (hM : 0 < M) :
    (∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
      ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ idealDivisors D, (UniqueFactorizationMonoid.moebius E : ℂ) *
        cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ)) := by
  rw [cubic_gcd_mobius_descent D hD cols hc a]
  apply Finset.sum_congr rfl
  intro E hE
  have hE0 : E ≠ 0 := by
    intro he
    have hh := (mem_idealDivisors (primaryGenerator_ne_zero_ideal D hD)).mp hE
    rw [he, zero_dvd_iff] at hh
    exact primaryGenerator_ne_zero_ideal D hD hh
  have hgen := idealGenerator_ne_zero E hE0
  congr 1
  rw [dividedMajorant_tsum _ _ hgen M hM, span_idealGenerator]
  apply majorant_coprime_tsum
  have hNE : 0 < (Ideal.absNorm E : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
  exact div_pos hM hNE

lemma gcdPool_cubic_admissible {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (D : Ideal O) (hD : D ∈ gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact cubic_admissible_of_dvd (hc j) (gcd_dvd_left _ _)

lemma gcdPool_subset_columnDivisorPool {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, cols j ≠ 0) :
    gcdPool cols ⊆ columnDivisorPool cols := by
  intro D hD
  obtain ⟨⟨j,k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact mem_columnDivisorPool_of_dvd cols hc j _ (gcd_dvd_left _ _)

theorem finite_energy_le_compact_descendants {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j)) (a : n → ℂ)
    (R : Finset O) (M : ℝ) (hM : 0 < M)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) :
    (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z * a j‖^2) ≤
      ∑ D ∈ gcdPool cols, ∑ E ∈ idealDivisors D,
        ‖cubicSmoothedCoprime (fun j => totalQuotient D (cols j))
          (descendedCoefficient D cols a (idealGenerator E)) rowMajorant
          (M / (Ideal.absNorm E : ℝ))‖ := by
  have hs := finite_row_energy_le_rowMajorant
    (fun z => ∑ j, cubicRow (cols j) z * a j) R M hM hR
  apply hs.trans
  apply (Complex.re_le_norm _).trans
  rw [rowMajorant_tsum_eq_sum _ M hM,
    cubic_weighted_energy_eq_gcd_blocks (rowMajorantBall M) _ cols a]
  have he (D : Ideal O) (hD : D ∈ gcdPool cols) :=
    compact_gcd_mobius_descent D (gcdPool_cubic_admissible cols hc D hD).2 cols hc a M hM
  calc
    _ ≤ ∑ D ∈ gcdPool cols,
        ‖∑ z ∈ rowMajorantBall M, rowMajorant (‖eisEmbedding z‖^2 / M) *
          ∑ j, ∑ k, cubicGcdTerm D cols a z j k‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro D hD
      rw [he D hD]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (QuadraticInitialBound.norm_ideal_moebius_le_one E)
        (norm_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.CubicSieve

end OAI
