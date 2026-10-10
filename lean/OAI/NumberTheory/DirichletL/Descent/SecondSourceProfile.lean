import OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def expansionProfileData (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (A₁ A₂ : Finset ι) (x : SecondExpansionData ι) : SecondProfileData ι where
  common := x.sourceCommon
  overlap := x.overlap
  extractedLeft := A₁ ∪ x.sourceCommon
  extractedRight := A₂ ∪ x.sourceCommon
  rayLeft := secondRayMinus Ψ z
  rayRight := secondRayPlus Ψ z
  puncture := m
  quotient := secondExpansionQuotient p x
  oldLabel := c
  oldDivisor := d
  divisor := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  frequency := x.frequency

def expansionProfileWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (Y : ℝ) (x : SecondExpansionData ι) : ℂ :=
  (Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondExpansionSource_marked_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    ∑ x ∈ source, expansionProfileWeight p hp hcop hg Ψ m c d z Y x *
      actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  have he := hE x hx
  have hc := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    x.sourceCommon x.divisor he F x.overlap Ψ Ψ m c d x.frequency z
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ (x.sourceCommon ∪ U)) *
        W₁ (primeProductNorm p (x.sourceCommon ∪ U)/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ (x.sourceCommon ∪ U)) *
        W₂ (primeProductNorm p (x.sourceCommon ∪ U)/X)) Φ Y)
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ ((A₁ ∪ x.sourceCommon) ∪ U) *
        W₁ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ ((A₂ ∪ x.sourceCommon) ∪ U) *
        W₂ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X)) Φ Y)
    (by
      intro S T hGS hGT
      simp only [secondSourcePairKernel,primeProductNorm_union p x.sourceCommon S hGS,
        primeProductNorm_union p x.sourceCommon T hGT,Finset.union_assoc])
  dsimp only at hc
  rw [← secondExpansionQuotient_of_subset p x he] at hc
  rw [hc]
  simp only [expansionProfileWeight,actualSecondProfileRow,expansionProfileData,
    secondSourceCommonCoefficient,Complex.ofReal_pow]
  ring

end
end SevenEighths.InverseMoment

end OAI
