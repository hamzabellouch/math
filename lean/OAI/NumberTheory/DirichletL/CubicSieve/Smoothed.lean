import OAI.NumberTheory.DirichletL.CubicSieve.DualCoefficients

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicRow_norm_le_one (I : Ideal O) (hI : Admissible I) (z : O) : ‖cubicRow I z‖ ≤ 1 :=
  elementCharacter_norm_le_one I hI.2 z

lemma cubic_pair_fourier_summable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) :
    Summable (fun h : O => (cubicRow I h * star (cubicRow J h)) *
      paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) _
    (paperRadialFourier_lattice_summable_norm W t ht)
  intro h
  simp only [norm_mul, norm_star]
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_right (cubicRow_norm_le_one I hI h) (norm_nonneg _)).trans
      (by simpa only [one_mul] using cubicRow_norm_le_one J hJ h))
    (norm_nonneg _)).trans_eq (one_mul _)

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖eisEmbedding z‖ ^ 2 / M) else 0

lemma pair_modulus_norm_sq (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    ‖eisEmbedding (primaryGenerator I * primaryGenerator J)‖ ^ 2 =
      (Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) := by
  rw [map_mul, norm_mul, mul_pow, primaryGenerator_norm_sq I hI.2, primaryGenerator_norm_sq J hJ.2]

lemma cubicDualRow_summable {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (cubicDualRow cols hc a W M) := by
  apply summable_sum
  intro j hj
  apply summable_sum
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · simp only [ite_eq_left hcop]
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    have hs := (cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity)).mul_left
      (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
        ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    convert hs using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  · simp only [ite_eq_right hcop]
    exact summable_zero

lemma cubicDualRow_tsum {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' h : O, cubicDualRow cols hc a W M h) =
      ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ))) *
          ∑' h : O, (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) else 0 := by
  have hs (j k : n) : Summable (fun h : O => (cubicRow (cols j) h * star (cubicRow (cols k) h)) *
      paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {h}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))) := by
    have hjN : 0 < (Ideal.absNorm (cols j) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc j).2))
    have hkN : 0 < (Ideal.absNorm (cols k) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryGenerator_ne_zero_ideal _ (hc k).2))
    convert cubic_pair_fourier_summable (cols j) (cols k) (hc j) (hc k) W
      (M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ))) (by positivity) using 1
    ext z
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [show M / ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) *
      (Ideal.absNorm (Ideal.span {z}) : ℝ) = M * (Ideal.absNorm (Ideal.span {z}) : ℝ) /
        ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) by ring]
    try simp only [mul_assoc]
  unfold cubicDualRow
  rw [Summable.tsum_finsetSum (fun j hj => summable_sum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Summable.tsum_finsetSum (fun k hk => by
    split_ifs
    · simpa only [mul_assoc] using (hs j k).mul_left
        (star (a j) * a k * (star (gaussTwo (cols j) (hc j).2) * gaussTwo (cols k) (hc k).2) /
          ((‖eisEmbedding (primaryGenerator (cols j))‖ : ℂ) * (‖eisEmbedding (primaryGenerator (cols k))‖ : ℂ)))
    · exact summable_zero)]
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs <;> simp only [tsum_zero, mul_assoc, tsum_mul_left]

theorem cubicSmoothedCoprime_poisson {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    cubicSmoothedCoprime cols a W M =
      (M : ℂ) * ∑' h : O, cubicDualRow cols hc a W M h := by
  rw [cubicDualRow_tsum cols hc a W M hM]
  unfold cubicSmoothedCoprime
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hcop : IsCoprime (cols j) (cols k)
  · rw [ite_eq_left hcop, ite_eq_left hcop, cubic_pair_poisson _ _ (hc j) (hc k) hcop W M hM]
    rw [pair_modulus_norm_sq _ _ (hc j) (hc k)]
    simp_rw [eisEmbedding_norm_sq_eq_absNorm_span]
    rw [map_mul, norm_mul, Complex.ofReal_mul]
    ring
  · simp only [ite_eq_right hcop, mul_zero]

end
end SevenEighths.CubicSieve

end OAI
