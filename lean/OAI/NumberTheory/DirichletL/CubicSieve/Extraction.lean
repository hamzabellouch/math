import OAI.NumberTheory.DirichletL.CubicSieve.Norm

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem primary_extracted_parts (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    primaryGenerator (firstPart I) ≠ 0 ∧ primaryGenerator (secondPart I) ≠ 0 ∧
      primaryGenerator (cubePart I) ≠ 0 := by
  have he := congrArg primaryGeneratorHom
    (cubic_factorization I (primaryGenerator_ne_zero_ideal I hI))
  simp only [map_mul, map_pow] at he
  change primaryGenerator I = primaryGenerator (firstPart I) *
    primaryGenerator (secondPart I) ^ 2 * primaryGenerator (cubePart I) ^ 3 at he
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem firstPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (firstPart I) := ⟨firstPart_squarefree I, (primary_extracted_parts I hI).1⟩

theorem secondPart_admissible (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    Admissible (secondPart I) := ⟨secondPart_squarefree I, (primary_extracted_parts I hI).2.1⟩

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  apply family_squared_norm_le (fun I : idealRange M => I.val)
    (fun J : idealRange N => J.val) Subtype.val_injective Subtype.val_injective M' N'
  · intro I
    exact ⟨(mem_idealRange.mp I.property).1, (mem_idealRange.mp I.property).2.trans hM⟩
  · intro J
    exact ⟨(mem_idealRange.mp J.property).1, (mem_idealRange.mp J.property).2.trans hN⟩

end
end SevenEighths.CubicSieve

end OAI
