import OAI.NumberTheory.DirichletL.Descent.SecondParentRadial
import OAI.NumberTheory.DirichletL.Descent.SecondCenterSector

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_parent_full_second_source
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X height Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (R : Finset ι → Finset ι → ℝ) (label : Finset ι → SecondExpansionData ι → κ) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let V := principalWindow om a b ha hs negative height
    let H₀ := markedRadial p slots lists coeff ∅ V X
    let K := secondVariableCutoff p parent R
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core height Y =
    truncatedSecondZero p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈F.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector F K residual label j).image (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
            actualSecondProfileRow p hp hcop hg F (secondInheritedProfile p x Ψ₀ m ray)
              slots slots lists lists coeff coeff V V rowMajorant Y X) +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ V H₀ K
  have htest : H₀=(fun U=>primeMark slots lists coeff U*V (primeProductNorm p U/X)) := by
    funext U
    simp only [H₀,markedRadial,Finset.empty_union]
  have hret := truncated_second_attached_variable p hp hcop hg hinj hc hpr parent F Ψ₀ m
    slots lists coeff V rowMajorant X Y R label
  rw [←htest] at hret
  calc
    _ = truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
          (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K :=
      first_fresh_parent_radial_truncated p hp hg hinj hc parent F D hq negative χ Ψ m
        slots lists coeff hD om a b ha hs X height Y hX hY core K
    _ = _ := congrArg (fun v=>v + secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K) hret

end
end SevenEighths.InverseMoment

end OAI
