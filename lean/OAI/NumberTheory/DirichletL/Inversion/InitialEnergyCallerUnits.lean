import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllSlots

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerUnits
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def sourceSector (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)=u)

omit [∀i,(Ideal.span {p i}).IsMaximal] in
theorem sourceSector_partition (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(f:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,f x)=∑u:Eisˣ,∑x∈sourceSector p hp hpr S u,f x :=
  (Finset.sum_fiberwise S (fun x=>unitSector p hp hpr (sourcePoint x ∅ ∅)) f).symm

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem quotientSet_mono {J:ℕ}{S T:Finset (Source (ι:=ι) J)}(hst:S⊆T) :
    quotientSet p S⊆quotientSet p T := Finset.image_subset_image hst

theorem unit_sector_card : Fintype.card Eisˣ=6 := by
  simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six

theorem all_units_bound (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
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
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerAllSlots.all_slots_bound N U π hU hπ
  refine ⟨6*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (u:Eisˣ) :
      ‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
    have hs : sourceSector p hp hpr S u⊆S := Finset.filter_subset _ _
    apply hbound p hp hcop hg hinj hpr hc (sourceSector p hp hpr S u) u
      (fun x hx=>hdiv x (hs hx)) (fun x hx=>(Finset.mem_filter.mp hx).2)
      pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR
      (fun t ht=>hn t (quotientSet_mono p hs ht)) ρ z w
      (fun x hx=>hw x (hs hx)) labels rows hlabels hneg
      (fun x hx=>by
        have hh := hchild x (hs hx)
        rw [(Finset.mem_filter.mp hx).2] at hh
        exact hh) F E hE
    intro J₁ hJ₁ J₂ hJ₂ t ht
    exact hmoment J₁ hJ₁ J₂ hJ₂ t
      (quotientSet_mono p hs (InverseInitialEnergyCallerMass.assigned_quotient_subset
        p (sourceSector p hp hpr S u) J₁ J₂ lists lists ht))
  rw [sourceSector_partition p hp hpr S]
  calc
    _≤∑u:Eisˣ,‖∑x∈sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j
      slots lists a ω₁ ω₂ Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑_u:Eisˣ,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun u _=>hb u
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,unit_sector_card,nsmul_eq_mul];norm_num;ring

end SevenEighths.InverseInitialEnergyCallerUnits

end

end OAI
