import OAI.NumberTheory.DirichletL.Descent.SecondFreshTruncation

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_parent_radial_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  let m₀ := (m*b0Label p parent.cube.support
    (fun i=>parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i
  have he (k : Eis) : inputConjugateRow p hg F Ψ₀ m₀
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k := by
    calc
      _ = inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
          (secondParentDivisor p parent) H₀ k := by
        unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
        apply Finset.sum_congr rfl
        intro U hU
        rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
      _ = _ := fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀ k
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
      (secondParentDivisor p parent) H k‖^2 : ℝ)) = _
  simp_rw [he]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
