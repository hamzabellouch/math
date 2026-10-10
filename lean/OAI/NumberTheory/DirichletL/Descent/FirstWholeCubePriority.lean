import OAI.NumberTheory.DirichletL.Descent.FirstActualPriorityEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_whole_cube_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (fun U=>primeMark slots lists a (extra∪U)) selector ω X t Y ≤
    firstWholePrioritySecondEnergy p hp hg hinj F b C extra negative Ψ m d slots lists a selector ω X t Y := by
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    simp only [Finset.union_assoc]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI
