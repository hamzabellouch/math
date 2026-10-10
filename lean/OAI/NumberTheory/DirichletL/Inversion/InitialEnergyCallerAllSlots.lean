import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerBranch
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerMass

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerAllSlots
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowMode_sum_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(u:Eisˣ)
    (hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(w:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z)=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  calc
    _=∑x∈S,∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rowMode_eq_allocations p hp hcop hg hpr x (hdiv x hx) u (hu x hx)]
      simp only [Finset.mul_sum]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.sum_comm

theorem all_slots_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(_hdiv:∀x∈S,x.divisor⊆x.common)
      (_hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hmass⟩ := InverseInitialEnergyCallerMass.assigned_quotient_mass (2*N) U π hU hπ
  refine ⟨C*4^N,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S u hdiv hu pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let bound := C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E
  have hb (J₁:Finset σ)(hJ₁:J₁∈slots.powerset)(J₂:Finset σ)(hJ₂:J₂∈slots.powerset) :
      ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤bound := by
    have h₁ := Finset.mem_powerset.mp hJ₁
    have h₂ := Finset.mem_powerset.mp hJ₂
    have he := actual_allocated_mode_bound p hp hcop hg hinj hpr hc S u hdiv pool Ψ hΨ j
      slots J₁ J₂ lists a (fun i hi=>ha i (h₁ hi)) (fun i hi=>ha i (h₂ hi)) ω₁ ω₂
      Z D B v θ H hZp ρ z w hw labels rows hlabels hneg hchild F E E
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).1)
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [Real.mul_self_sqrt hE] at he
    have hJ : J₁.card+J₂.card≤2*N := by
      have := (Finset.card_le_card h₁).trans hslots
      have := (Finset.card_le_card h₂).trans hslots
      omega
    have hm := hmass p hp S J₁ J₂ lists lists hJ Z R hZ hR hn
    apply he.trans
    calc
      _≤‖secondRayCoefficient ρ‖*(Z^F*(C*Z^(R+π)))*E := by gcongr
      _=bound := by dsimp only [bound];rw [add_assoc F R π,Real.rpow_add hZp F (R+π)];ring
  rw [rowMode_sum_allocations p hp hcop hg hpr S hdiv u hu]
  calc
    _≤∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ‖∑x∈S,w x*allocatedMode p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun J hJ=>norm_sum_le _ _)
    _≤∑_J₁∈slots.powerset,∑_J₂∈slots.powerset,bound :=
      Finset.sum_le_sum fun J₁ hJ₁=>Finset.sum_le_sum fun J₂ hJ₂=>hb J₁ hJ₁ J₂ hJ₂
    _=(4:ℝ)^slots.card*bound := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _≤(4:ℝ)^N*bound := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hslots) (by dsimp [bound];positivity)
    _=_ := by dsimp [bound];ring

end SevenEighths.InverseInitialEnergyCallerAllSlots

end

end OAI
