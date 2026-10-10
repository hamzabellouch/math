import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllocation

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerBranch
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_allocated_mode_bound
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(hdiv:∀x∈S,x.divisor⊆x.common)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈lists i,‖a i q‖≤1)(ha₂:∀i∈J₂,∀q∈lists i,‖a i q‖≤1)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)(hZ:0<Z)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (w:Source (ι:=ι) 0→ℂ)(hw:∀x∈S,‖w x‖≤1)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤B₂) :
    ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
      Z D B v θ H x ρ z‖≤
      ‖secondRayCoefficient ρ‖*(Z^F*∑t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let c := fun x=>w x*modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z
  have hcoeff (x:Source (ι:=ι) 0)(hx:x∈S) : ‖c x‖≤‖secondRayCoefficient ρ‖ := by
    dsimp only [c]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x hx)).trans
      (modeCoefficient_norm_le p hp hcop hg hc Ψ hΨ j Z D B v θ H x ρ z)
  have he := InverseInitialEnergyCallerAssignedCanonical.original_assigned_canonical_pair
    p hp hcop hg hinj hpr S u J₁ J₂ lists lists a a ha₁ ha₂ hdiv labels rows hlabels hneg hchild
    c ‖secondRayCoefficient ρ‖ (norm_nonneg _) hcoeff pool (secondRayMinus Ψ ρ) (secondRayPlus Ψ ρ) j
    (slots\J₁) (slots\J₂)
    (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
    (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
    (Z^(columnCenter D B v)) (Z^(columnCenter D B v)) hZ F B₁ B₂ hmoment₁ hmoment₂
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [allocatedMode,c]
  ring

end SevenEighths.InverseInitialEnergyCallerBranch

end

end OAI
