import OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
import OAI.NumberTheory.DirichletL.Descent.SecondParentInput

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_radial_truncated
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K := by
  intro H₀ Ψ₀ m₀ c₀
  rw [firstFreshSecondPoisson_markedRadial p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X t Y hX hY c d r]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
