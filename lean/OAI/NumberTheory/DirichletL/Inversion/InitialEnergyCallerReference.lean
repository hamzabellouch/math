import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerUniform

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
namespace SevenEighths.InverseInitialEnergyCallerReference
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

theorem actual_physical_reference_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p S,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cp,hCp,hphysical⟩ := InverseInitialEnergyCallerPhysical.actual_physical_block_bound
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox (4*J) N U π hU hπ
  refine ⟨Cp*(C₁+C₂),mul_pos hCp (add_pos hC₁ hC₂),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hm : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p S,
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      gcongr
      linarith
    · apply hb₂.trans
      gcongr
      linarith
  have hb := hphysical p hp hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    ω₁ ω₂ Z D B v θ H R m η hZ.le hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F ((C₁+C₂)*(A*Z^(F+ε))) (by positivity) hm
  apply hb.trans
  have he : prefactorCenter m D B θ+3*η+F+R+π+(F+ε)≤m+11*η+π+ε := by
    rw [hF,hReq]
    exact InverseInitialEnergyCallerClipping.initial_scalar_le m D B v θ η _ π ε hδ
  have hexp := Real.rpow_add hZp (prefactorCenter m D B θ+3*η+F+R+π) (F+ε)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(Cp*(C₁+C₂))*Z^(prefactorCenter m D B θ+3*η+F+R+π+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by rw [hexp];ring
    _≤_ := by gcongr

end SevenEighths.InverseInitialEnergyCallerReference

end

end OAI
