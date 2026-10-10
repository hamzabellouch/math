import OAI.NumberTheory.DirichletL.CubicSieve.ExtractionBounds

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

def extractionLabel (M : ℝ) (z : O) :
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) :=
  (CanonicalQuadraticSieve.divisorDyadicLabel M (firstPart (Ideal.span {z})),
   CanonicalQuadraticSieve.divisorDyadicLabel M (secondPart (Ideal.span {z})))

def extractionBin (R : Finset O) (M : ℝ)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)) : Finset O :=
  R.filter (fun z => extractionLabel M z = j)

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end SevenEighths.CubicSieve

end OAI
