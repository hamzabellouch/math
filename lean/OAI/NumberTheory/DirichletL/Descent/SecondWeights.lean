import OAI.NumberTheory.DirichletL.Descent.SecondSourceProfile

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSignedSourceWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap

theorem expansionProfileWeight_eq_signed (Ψ : Eis →* ℂ) (m c d : Eis)
    (z : SecondRayIndex) (Y : ℝ) (x : SecondExpansionData ι) :
    expansionProfileWeight p hp hcop hg Ψ m c d z Y x =
      (Y : ℂ)*secondRayCoefficient z*secondSignedSourceWeight p hp hcop hg Ψ m c d z x := by
  simp only [expansionProfileWeight,secondSignedSourceWeight,secondTotalWeight]
  ring

theorem secondSignedSourceWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) :
    ‖secondSignedSourceWeight p hp hcop hg Ψ m c d z x‖ ≤ 1 := by
  have hinput : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one
    (∏ i ∈ x.divisor,Ideal.span {p i})
  have hcommon := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency) x.overlap
  have hc1 : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap‖ ≤ 1 := by
    apply hcommon.trans
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((secondRayMinus_norm_le Ψ z _).trans (hΨ _))).trans
      ((secondRayPlus_norm_le Ψ z _).trans (hΨ _))
  simp only [secondSignedSourceWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖))]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hinput).trans hμ)).trans hc1

theorem secondExpansionSource_signed_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x ∈ source, secondSignedSourceWeight p hp hcop hg Ψ m c d z x *
        actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [secondExpansionSource_marked_profile p hp hcop hg hinj hpr (hE := hE)]
  simp only [expansionProfileWeight_eq_signed,Finset.mul_sum,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
