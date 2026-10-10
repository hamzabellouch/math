import OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
import OAI.NumberTheory.DirichletL.Descent.SecondFiniteMeasure

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure SecondProfileData (ι : Type*) where
  common : Finset ι
  overlap : Finset ι
  extractedLeft : Finset ι
  extractedRight : Finset ι
  rayLeft : Eis →* ℂ
  rayRight : Eis →* ℂ
  puncture : Eis
  quotient : Eis
  oldLabel : Eis
  oldDivisor : Eis
  divisor : Eis
  frequency : Eis

def secondActualNorms {ι : Type*} (p : ι → Eis) (x : SecondProfileData ι)
    (N M : Finset ι) : Fin 6 → ℝ :=
  ![primeProductNorm p x.common, ‖eisEmbedding x.divisor‖^2,
    primeProductNorm p x.overlap, ‖eisEmbedding x.frequency‖^2,
    primeProductNorm p N, primeProductNorm p M]

lemma secondActualNorms_pos {ι : Type*} (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (x : SecondProfileData ι) (he : x.divisor ≠ 0) (hk : x.frequency ≠ 0) (N M : Finset ι) :
    ∀ i, 0 < secondActualNorms p x N M i := by
  intro i
  fin_cases i
  · exact primeProductNorm_pos p hp x.common
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  · exact primeProductNorm_pos p hp x.overlap
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hk))
  · exact primeProductNorm_pos p hp N
  · exact primeProductNorm_pos p hp M

def secondActualCoefficient {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (N M : Finset ι) : ℂ :=
  star (secondChildColumn p hp hcop hg x.rayLeft (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*x.frequency) (fun _ => 1) N) *
  secondChildColumn p hp hcop hg x.rayRight (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*(-x.frequency)) (fun _ => 1) M *
  (star (primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ (x.overlap ∪ N))) *
    primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ (x.overlap ∪ M)))

def actualSecondProfileRow {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) : ℂ :=
  (‖eisEmbedding x.divisor‖^2 : ℂ)⁻¹ *
  secondChildKernelPair p hp hcop hg F x.overlap x.rayLeft x.rayRight x.puncture x.quotient
    x.oldLabel x.oldDivisor x.divisor x.frequency (-x.frequency)
    (secondSourcePairKernel p x.divisor x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ U)*
        W₁ (primeProductNorm p x.common*primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ U)*
        W₂ (primeProductNorm p x.common*primeProductNorm p U/X)) Φ Y)

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hcop hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end SevenEighths.InverseMoment

end OAI
