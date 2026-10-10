import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerSector

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerAllocation
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerSector
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def modeCoefficient (Ψ:Eis→*ℂ)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  outerCoefficient p hp hcop hg Ψ j (sourcePoint x ∅ ∅) ρ *
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2)
      (relativeLog (coordinates p (sourcePoint x ∅ ∅)) Z D B v θ H)

def allocatedMode (u:Eisˣ)(pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z *
    (star (primeMark J₁ lists a (x.common∪x.overlap))*primeMark J₂ lists a (x.common∪x.overlap))*
    (star (child p hp hcop hg pool (secondRayMinus Ψ ρ) j (slots\J₁) lists a
      (childLogTest ω₁ (-height 4)) (Z^(columnCenter D B v))
      (initialChild (toTuple p (sectorSource u x))))*
      child p hp hcop hg pool (secondRayPlus Ψ ρ) j (slots\J₂) lists a
      (childLogTest ω₂ (height 5)) (Z^(columnCenter D B v))
      (negativeChild (initialChild (toTuple p (sectorSource u x)))))

theorem rowMode_eq_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  unfold rowMode
  dsimp only
  rw [markedModeColumn_sector p hp hcop hg hpr x hdiv u hu,
    markedModeColumn_negative_sector p hp hcop hg hpr x hdiv u hu]
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  simp only [star_mul,allocatedMode,modeCoefficient]
  ring

theorem modeCoefficient_norm_le
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    ‖modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z‖≤‖secondRayCoefficient ρ‖ := by
  simp only [modeCoefficient,norm_mul,secondOuterPhase_norm,mul_one]
  exact InverseInitialEnergyCallerWeights.outerCoefficient_norm_le p hp hcop hg hc Ψ hΨ j _ ρ

end SevenEighths.InverseInitialEnergyCallerAllocation

end

end OAI
