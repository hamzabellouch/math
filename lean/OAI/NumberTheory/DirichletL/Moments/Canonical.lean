import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Moments.PrimePower
import OAI.NumberTheory.DirichletL.Moments.CRT

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

def primePowerRow (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P)
    {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) : ℂ :=
  (actualSextic P hg ^ c) (primePowerReduction P hc x)

theorem canonical_primePower_units (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      actualSextic P hg (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_second_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_second_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_first_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : O ⧸ P ^ c) (v : (O ⧸ P ^ c)ˣ) (k : O ⧸ P ^ c)
    (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : O ⧸ P ^ c) * x) (fun y => u * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0 then (Ideal.absNorm P : ℂ) - 1 else 0) :=
  primePower_localCorrelation_first_zero P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hu

def canonicalPrimePowerCharacter (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) : MulChar (O ⧸ P ^ c) ℂ :=
  primePowerCharacter P hc (actualSextic P hg ^ c)

theorem canonicalPrimePowerCharacter_mk (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) {c : ℕ} (hc : 1 ≤ c) (x : O) :
    canonicalPrimePowerCharacter P hg hc (Ideal.Quotient.mk (P ^ c) x) =
      CanonicalRowCompletion.idealRowHom x (P ^ c) := by
  change (actualSextic P hg ^ c) (Ideal.Quotient.mk P x) = _
  rw [MulChar.pow_apply' _ (by omega), map_pow,
    CanonicalRowCompletion.idealRowHom_prime x P hg]

private theorem pairwise_isCoprime_pow {ι : Type*}
    (P : ι → Ideal O) (c : ι → ℕ)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    Pairwise (Function.onFun IsCoprime (fun i => P i ^ c i)) := by
  intro i j hij
  exact (hcop hij).pow

def canonicalCRTCharacter {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ ∏ i, P i ^ c i) ℂ :=
  crtCharacter (IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
    (pairwise_isCoprime_pow P c hcop))
    (fun i => canonicalPrimePowerCharacter (P i) (hg i) (hc i))

theorem canonicalCRTCharacter_mk {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    canonicalCRTCharacter P hg c hc hcop (Ideal.Quotient.mk (∏ i, P i ^ c i) x) =
      CanonicalRowCompletion.idealRowHom x (∏ i, P i ^ c i) := by
  simp only [canonicalCRTCharacter, crtCharacter_apply,
    IdealGaussCRT.quotientProdEquivPi_mk, canonicalPrimePowerCharacter_mk, map_prod]

theorem canonicalCRTCorrelation {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i ^ c i)] [∀ i, Fintype (O ⧸ P i ^ c i)]
    (u v k : O ⧸ ∏ i, P i ^ c i) :
    let e := IdealGaussCRT.quotientProdEquivPi (fun i => P i ^ c i)
      (pairwise_isCoprime_pow P c hcop)
    fullCorrelation (fun x => v * x) (fun y => u * y)
      (canonicalCRTCharacter P hg c hc hcop) (canonicalCRTCharacter P hg c hc hcop) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (primePowerRow (P i) (hg i) (hc i)) (primePowerRow (P i) (hg i) (hc i))
        (e k i) := by
  dsimp only
  change fullCorrelation (fun x => v * x) (fun y => u * y)
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i)
      (IdealGaussCRT.quotientProdEquivPi _ _ x i)) k = _
  rw [fullCorrelation_ringEquiv (IdealGaussCRT.quotientProdEquivPi _ _) u v k
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i))
    (fun x => ∏ i, primePowerRow (P i) (hg i) (hc i) (x i)), fullCorrelation_pi]

end SevenEighths.CenteredMomentCanonical
end

end OAI
