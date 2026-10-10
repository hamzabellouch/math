import OAI.NumberTheory.DirichletL.Moments.FixedRay
import OAI.NumberTheory.DirichletL.CenteredExceptionalProfile

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildRows
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily HeckeRowClosure
open CenteredMomentFixedRay RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def childCharacter (η : Character) (χ : RayCharacter) : Character :=
  η.product (primaryRayCharacter χ)

@[simp] theorem childCharacter_modulus (η : Character) (χ : RayCharacter) :
    (childCharacter η χ).modulus = η.modulus ⊓ Ideal.span {(12 : O)} := rfl

theorem childCharacter_primary (η : Character) (χ : RayCharacter) (n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    elementCoeff (childCharacter η χ) n = elementCoeff η n * rayCharacter χ n := by
  rw [childCharacter, elementCoeff_product, primaryRayCharacter_primary χ n hn hp]

theorem child_row_primary (η : Character) (χ : RayCharacter) (m A h n : O)
    (hn : Supported (Ideal.span {n})) (hp : λ₀^2 ∣ n - 1) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n =
      (elementCoeff η n * rayCharacter χ n) * coprimalityMask m n *
        idealRowHom (A*h) (Ideal.span {n}) := by
  rw [rowTwist_extract_sixth_mask _ m 1 (A*h) n hn]
  change elementCoeff (childCharacter η χ) n * _ * _ = _
  rw [childCharacter_primary η χ n hn hp]
  simp only [one_pow, one_mul]

theorem child_row_extract (η : Character) (χ : RayCharacter) (m A h e n : O) :
    rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) (e*n) =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) e *
        rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n := map_mul _ _ _

theorem exists_child_row_character (η : Character) (χ : RayCharacter) (m A h : O)
    (hm : m ≠ 0) (hA : A ≠ 0) (hh : h ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ ρ : Character, ∀ n, elementCoeff ρ n =
      rowTwist (elementHom (childCharacter η χ)) m 1 (A*h) n :=
  exists_row_character (childCharacter η χ) m 1 (A*h) hm one_ne_zero (mul_ne_zero hA hh) hmLam hm2

theorem old_coefficient_nonzero_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) : IsCoprime (Ideal.span {e}) η.modulus :=
  (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp he)

theorem old_coefficient_prime_coprime (η : Character) (e : O)
    (he : elementCoeff η e ≠ 0) (P : Ideal O) (hP : P ∣ Ideal.span {e}) :
    IsCoprime η.modulus P :=
  (old_coefficient_nonzero_coprime η e he).symm.of_isCoprime_of_dvd_right hP

theorem childCharacter_coprime (η : Character) (χ : RayCharacter) (Q P : Ideal O)
    (hQ : Q ≤ Ideal.span {(72 : O)}) (hQP : IsCoprime Q P)
    (hηP : IsCoprime η.modulus P) : IsCoprime (childCharacter η χ).modulus P := by
  have h12 : IsCoprime (Ideal.span {(12 : O)}) P :=
    hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr (hQ.trans
      (Ideal.span_singleton_le_span_singleton.mpr ⟨6, by norm_num⟩)))
  rw [childCharacter_modulus]
  exact (hηP.mul_left h12).of_isCoprime_of_dvd_left
    (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

theorem separated_exceptional_count (η : Character) (χ : RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m A e : O) (hm : m ≠ 0) (hA : A ≠ 0) (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m A z)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D,
      λ₀ ∉ P ∧ (2 : O) ∉ P ∧ IsCoprime Q P ∧ P ∣ Ideal.span {e} ∧
        CenteredExceptionalCount.valuation (Ideal.span {A}) P % 6 = 2)
    (Z C M F : ℝ) (hZ : 0 < Z) (hC : 0 ≤ C)
    (hDnorm : Z ^ (F / 2) ≤ (Ideal.absNorm D : ℝ))
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) * Z ^ ((M - 2 * F) / 6) := by
  apply CenteredExceptionalProfile.fixed_support_exceptional_count
    (childCharacter η χ) Q hQ0 hQ hQ72 m A hm hA hmLam hm2 T hT hex D hD
      ?_ Z C M F hZ hC hDnorm hN
  intro P hP
  obtain ⟨hg,h2,hQP,hPe,hval⟩ := hgood P hP
  exact ⟨hg,h2,hQP,childCharacter_coprime η χ Q P hQ72 hQP
    (old_coefficient_prime_coprime η e he P hPe),hval⟩

end SevenEighths.CenteredMomentChildRows

end

end OAI
