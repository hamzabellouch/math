import OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily
import OAI.NumberTheory.DirichletL.Descent.FirstPriorityEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalSecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  (32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
        (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)) ω X (∏i∈C,p i) d core t Y).re

theorem firstCanonicalSecondEnergy_nonneg (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    0≤firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d H selector ω X t Y := by
  unfold firstCanonicalSecondEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro core hcore
  apply mul_nonneg (norm_nonneg _)
  rw [first_fresh_real_energy p hp hg hinj hc F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m _ ω X (∏i∈C,p i) d core t Y hY]
  exact Finset.sum_nonneg (fun z hz=>mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _))

theorem first_retained_actual_second_energy (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (labels : Finset (Ideal O)) (a : Ideal O×O→ℂ) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ f∈labels,Squarefree f) → (∀ f∈labels,f≠0) → (∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ) →
      ∀ (negative : Bool) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t : ℝ),0<X →
      firstFamilyEnergy p hg (firstRetainedSource p labels b Y) F (fun _=>selector)
        (firstCanonicalCoefficient p hp hcop hg b C negative
          (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H)
        (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a) negative ω X t Prod.snd ≤
      Γ*K*Y^ε * firstCanonicalSecondEnergy p hp hg hinj F b C negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H selector ω X t Y := by
  obtain ⟨K,hK,hstep⟩ := retained_cube_energy_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d labels a Γ Y hΓ hY
    hlabels hn ha negative H selector ω X t hX
  have he := hstep p hp hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a
    (firstRetainedSource p labels b Y) Γ Y hΓ hY
    (fun x hx=>hlabels x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1)
    (fun x hx=>hn x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1) ha
    (fun x hx=>((mem_firstRetainedSource p labels b Y x).mp hx).2)
    negative H selector ω X t hX
  have hcoef : firstCanonicalCoefficient p hp hcop hg b C negative
      (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H =
      fun x=>firstOldLabelCoefficient p hp hcop hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂)
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := by
    funext x
    exact firstCanonicalCoefficient_old p hp hcop hg b C negative _ _ d H x
  rw [hcoef]
  exact he

end
end SevenEighths.InverseMoment

end OAI
