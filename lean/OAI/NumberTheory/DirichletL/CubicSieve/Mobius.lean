import OAI.NumberTheory.DirichletL.CubicSieve.Gcd

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def elementQuotient (d z : O) : O := if h : d ∣ z then h.choose else 0

lemma elementQuotient_mul (d z : O) (h : d ∣ z) : d * elementQuotient d z = z := by
  rw [elementQuotient, dite_eq_left h]
  exact h.choose_spec.symm

lemma elementQuotient_injective (d : O) : Set.InjOn (elementQuotient d) {z | d ∣ z} := by
  intro x hx y hy he
  rw [← elementQuotient_mul d x hx, ← elementQuotient_mul d y hy, he]

def dividedRows (R : Finset O) (d : O) : Finset O :=
  (R.filter (fun z => d ∣ z)).image (elementQuotient d)

lemma sum_divisible_rows (R : Finset O) (d : O) (f : O → ℂ) :
    (∑ z ∈ R, if d ∣ z then f z else 0) =
      ∑ w ∈ dividedRows R d, f (d * w) := by
  rw [← Finset.sum_filter]
  unfold dividedRows
  have hinj : Set.InjOn (elementQuotient d) (↑(R.filter (fun z => d ∣ z)) : Set O) := by
    intro x hx y hy he
    exact elementQuotient_injective d (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 he
  rw [Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro z hz
  rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]

lemma dividedRows_ne_zero (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0) (d : O)
    (w : O) (hw : w ∈ dividedRows R d) : w ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  intro he
  have h := elementQuotient_mul d z (Finset.mem_filter.mp hz).2
  rw [he, mul_zero] at h
  exact hR z (Finset.mem_filter.mp hz).1 h.symm

lemma dividedRows_norm_le (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (d : O) (hd : d ≠ 0) (w : O) (hw : w ∈ dividedRows R d) :
    (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ M / (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  have hdN : 0 < (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hd))
  apply (le_div_iff₀ hdN).mpr
  calc
    _ = (Ideal.absNorm (Ideal.span {d * elementQuotient d z}) : ℝ) := by
      rw [← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul, mul_comm]
    _ = (Ideal.absNorm (Ideal.span {z}) : ℝ) := by
      rw [elementQuotient_mul d z (Finset.mem_filter.mp hz).2]
    _ ≤ M := hR z (Finset.mem_filter.mp hz).1

lemma cubicRow_mul_argument (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    cubicRow I (x * y) = cubicRow I x * cubicRow I y := by
  exact (elementCharacter I hI).map_mul x y

lemma totalQuotient_cubic_admissible (D I : Ideal O) (hI : Admissible I) :
    Admissible (totalQuotient D I) := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    exact cubic_admissible_quotient hI h
  · rw [totalQuotient, ite_eq_right h]
    exact ⟨squarefree_one, by rw [primaryGenerator_one]; exact one_ne_zero⟩

def descendedCoefficient {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (d : O) (j : n) : ℂ :=
  cubicRow (totalQuotient D (cols j)) d * (if D ∣ cols j then a j else 0)

def residualGram {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
    star (cubicRow (totalQuotient D (cols j)) z * a j) *
      (cubicRow (totalQuotient D (cols k)) z * a k) else 0

lemma residualGram_rescale {n : Type*} [Fintype n] (D : Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (d w : O) :
    residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * w) =
      residualGram D cols (descendedCoefficient D cols a d) w := by
  unfold residualGram
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs
  · rw [cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols j)).2,
      cubicRow_mul_argument _ (totalQuotient_cubic_admissible D _ (hcols k)).2]
    simp only [descendedCoefficient, star_mul]
    ring
  · rfl

lemma ideal_dvd_span_iff_generator (E : Ideal O) (z : O) :
    E ∣ Ideal.span {z} ↔ idealGenerator E ∣ z := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have he : (z ∈ Ideal.span {idealGenerator E}) ↔ idealGenerator E ∣ z :=
    Ideal.mem_span_singleton
  rwa [span_idealGenerator] at he

lemma sum_dividedRows_residualGram_rescale {n : Type*} [Fintype n]
    (D : Ideal O) (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) (d : O) :
    (∑ z ∈ dividedRows R d,
      w (d * z) * residualGram D cols (fun j => if D ∣ cols j then a j else 0) (d * z)) =
      ∑ z ∈ dividedRows R d,
        w (d * z) * residualGram D cols (descendedCoefficient D cols a d) z := by
  apply Finset.sum_congr rfl
  intro z _
  rw [residualGram_rescale D cols hcols a]

theorem cubic_gcd_mobius_descent {n : Type*} [Fintype n]
    (D : Ideal O) (hD : primaryGenerator D ≠ 0)
    (cols : n → Ideal O) (hcols : ∀ j, Admissible (cols j))
    (a : n → ℂ) (R : Finset O) (w : O → ℂ) :
    (∑ z ∈ R, w z * ∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ dividedRows R (idealGenerator E),
            w (idealGenerator E * z) *
              residualGram D cols (descendedCoefficient D cols a (idealGenerator E)) z := by
  let b : n → ℂ := fun j => if D ∣ cols j then a j else 0
  have ht (z : O) : (∑ j, ∑ k, cubicGcdTerm D cols a z j k) =
      (star (cubicRow D z) * cubicRow D z) * residualGram D cols b z := by
    simp only [cubicGcdTerm_eq_quotient D (primaryGenerator_ne_zero_ideal D hD),
      residualGram, b, Finset.mul_sum]
  calc
    _ = ∑ z ∈ R, ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          (if idealGenerator E ∣ z then w z * residualGram D cols b z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ht, cubicRow_common_mobius D hD, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      rw [ideal_dvd_span_iff_generator]
      split_ifs <;> ring
    _ = ∑ E ∈ IdealMobiusDivisorSum.idealDivisors D,
        (UniqueFactorizationMonoid.moebius E : ℂ) *
          ∑ z ∈ R, if idealGenerator E ∣ z then w z * residualGram D cols b z else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [sum_divisible_rows]
      exact congrArg ((UniqueFactorizationMonoid.moebius E : ℂ) * ·)
        (sum_dividedRows_residualGram_rescale D cols hcols a R w (idealGenerator E))

end
end SevenEighths.CubicSieve

end OAI
