import OAI.NumberTheory.DirichletL.CubicSieve.GaussNorm

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def pairPrime (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → Ideal O :=
  Sum.elim Subtype.val Subtype.val

instance pairPrime_maximal (I J : Ideal O) (P : PrimeIndex I ⊕ PrimeIndex J) :
    (pairPrime I J P).IsMaximal := by
  cases P <;> exact primeIndexMaximal _ _

lemma pairPrime_good (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) : goodLambda ∉ pairPrime I J P := by
  cases P with
  | inl P => exact primeIndex_good I hI.2 P
  | inr P => exact primeIndex_good J hJ.2 P

lemma pairPrime_coprime (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (hcop : IsCoprime I J) : Pairwise (Function.onFun IsCoprime (pairPrime I J)) := by
  have cross (P : PrimeIndex I) (Q : PrimeIndex J) : IsCoprime P.val Q.val := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply top_unique
    rw [← hcop.sup_eq]
    exact sup_le_sup (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI.2) P)
      (primeIndex_le J (primaryGenerator_ne_zero_ideal J hJ.2) Q)
  intro P Q hPQ
  cases P with
  | inl P => cases Q with
    | inl Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime I (fun he => hPQ (congrArg Sum.inl he))
    | inr Q => exact cross P Q
  | inr P => cases Q with
    | inl Q => exact (cross Q P).symm
    | inr Q =>
      exact CanonicalRowCompletion.primeIndex_pairwise_coprime J (fun he => hPQ (congrArg Sum.inr he))

lemma pairPrime_product (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    (∏ P, pairPrime I J P) = I * J := by
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·) (primeIndex_product I hI) (primeIndex_product J hJ)

def pairExponent (I J : Ideal O) : PrimeIndex I ⊕ PrimeIndex J → ℕ :=
  Sum.elim (fun _ => 4) (fun _ => 2)

lemma pairExponent_nonprincipal (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (P : PrimeIndex I ⊕ PrimeIndex J) :
    actualSextic (pairPrime I J P) (pairPrime_good I J hI hJ P) ^ pairExponent I J P ≠ 1 := by
  cases P with
  | inl P => exact cubicExponent_nonprincipal P.val (primeIndex_good I hI.2 P) true
  | inr P => exact cubicExponent_nonprincipal P.val (primeIndex_good J hJ.2 P) false

lemma primeIndex_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z =
      cubicRow I z := by
  exact (CompletedGauss.cubicRow_mk I hI.2 z).symm.trans
    (CubicEisenstein.cubicRow_eq_idealSymbol I hI.2 hI.1 z)

lemma primeIndex_conjugate_cubic_row (I : Ideal O) (hI : Admissible I) (z : O) :
    finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      star (cubicRow I z) := by
  have he : finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z =
      (finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 2) z) ^ 2 := by
    simp only [finiteSexticRow, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro P hP
    rw [MulChar.pow_apply' _ (by decide : (4 : ℕ) ≠ 0),
      MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), ← pow_mul]
  rw [he, primeIndex_cubic_row I hI, cubicRow_square_eq_star]

lemma pairPrime_row (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (z : O) :
    finiteSexticRow (pairPrime I J) (pairPrime_good I J hI hJ) (pairExponent I J) z =
      star (cubicRow I z) * cubicRow J z := by
  unfold finiteSexticRow
  rw [Fintype.prod_sum_type]
  change finiteSexticRow (fun P : PrimeIndex I => P.val) (primeIndex_good I hI.2) (fun _ => 4) z *
    finiteSexticRow (fun P : PrimeIndex J => P.val) (primeIndex_good J hJ.2) (fun _ => 2) z = _
  rw [primeIndex_conjugate_cubic_row I hI, primeIndex_cubic_row J hJ]

lemma pairPrime_modulus (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) :
    Ideal.span {primaryGenerator I * primaryGenerator J} = ∏ P, pairPrime I J P := by
  rw [pairPrime_product I J hI hJ, ← Ideal.span_singleton_mul_span_singleton,
    (primaryGenerator_spec I hI.2).1, (primaryGenerator_spec J hJ.2).1]

end
end SevenEighths.CubicSieve

end OAI
