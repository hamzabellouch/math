import OAI.NumberTheory.DirichletL.CubicSieve.FullExtraction

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast CanonicalQuadraticSieve.goodSquarefreePart_norm_le I hI

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    DescentFiberCost.finite_ideal_count_real _ X hX
      (fun I hI => primaryGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    DescentFiberCost.finite_ideal_count_real _ Y hY
      (fun I hI => primaryGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end SevenEighths.CubicSieve

end OAI
