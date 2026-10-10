import OAI.NumberTheory.DirichletL.Descent.SecondCanonicalChild
import OAI.NumberTheory.DirichletL.Descent.SecondSourceProfile

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualMarkedSecondProfileData {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) (A₁ A₂ : Finset ι) : SecondProfileData ι :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  expansionProfileData p Ψ (m*b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit*d)
    c d z A₁ A₂ x.second

theorem actual_second_split_child_uniform
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (A : Finset ι), A ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon →
      ∀ (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor
      let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
      canonicalMarkedSplit p hp hcop hg F x.second.overlap A Ψ
        (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit*d)
        (secondExpansionQuotient p x.second) c d e k slots lists a W
        (primeProductNorm p x.second.overlap*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪x.second.overlap) *
        secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
          (slots\J) lists a (fun _ => W) X
          (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hchild⟩ := actual_second_canonical_child p hp hcop hg hpr (σ:=σ) x hE
  refine ⟨u,v,?_⟩
  intro F Ψ m k A hA slots lists a W X
  dsimp only
  rw [secondExpansionQuotient_of_subset p x.second hE]
  rw [actual_second_split_fixed_family p hp hcop hg F x.cube.support x.firstCommon
    x.firstDivisor x.second.sourceCommon x.second.divisor x.second.overlap A hCB hD hE hA
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    x.cube.support_pos Ψ m k slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simpa only [actualSecondRawLabel,secondExpansionQuotient_of_subset p x.second hE] using
    hchild F Ψ m k (slots\J) lists a W X

theorem actual_second_separated_pair_canonical
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}}) := by
  obtain ⟨u,v,hsplit⟩ := actual_second_split_child_uniform p hp hcop hg hpr (σ:=σ) x hCB hD hE
  refine ⟨u,v,?_⟩
  intro F Ψ m z A₁ A₂ hA₁ hA₂ slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t
  dsimp only
  have hA (A : Finset ι) (ha : A ⊆ x.cube.support∪x.firstCommon) :
      A∪x.second.sourceCommon ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon :=
    Finset.union_subset_union_left ha
  unfold secondSeparatedPair
  dsimp only [actualMarkedSecondProfileData,expansionProfileData]
  rw [hsplit F (secondRayMinus Ψ z) m x.second.frequency _ (hA A₁ hA₁),
    hsplit F (secondRayPlus Ψ z) m (-x.second.frequency) _ (hA A₂ hA₂)]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  ring

end
end SevenEighths.InverseMoment

end OAI
