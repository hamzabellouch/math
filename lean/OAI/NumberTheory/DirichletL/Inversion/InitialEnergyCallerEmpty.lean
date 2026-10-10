import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerEmpty
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialProfile InverseInitialClippedColumns InverseInitialKernelBridge
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_zero_of_fresh_empty
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂:ℝ)(hZ:0<Z)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (he:freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅) :
    physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0 := by
  unfold physicalBlock
  apply Finset.sum_eq_zero
  intro x hx
  have hv:=pointSource_valid pool S hdiv hf x hx
  have hleft:x.left⊆pool := by
    obtain ⟨s,hs,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
    exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  have hω:ω₁ (columnRatio p x.left Z D B v)=0 := by
    by_contra hn
    rw [columnRatio_actual] at hn
    have hm:= (mem_freshColumns p pool ω₁ (Z^(columnCenter D B v)) x.left).mpr ⟨hleft,hn⟩
    rw [he] at hm
    exact Finset.notMem_empty _ hm
  have hW:clippedSource W₁ c₁ θ₁
      (relativeNorm (coordinates p x) Z D B v θ H 0 *
        relativeNorm (coordinates p x) Z D B v θ H 2 *
        relativeNorm (coordinates p x) Z D B v θ H 4)=0 := by
    by_contra hn
    have hh:=hs.1 x hx hn
    simp only [hω,star_zero] at hh
    exact zero_ne_one hh
  apply Finset.sum_eq_zero
  intro ρ hρ
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j marks _ _ Φ Z D m x hv ρ,
    physicalKernel_nominal _ _ Φ hZ D B v m θ H _ (coordinates_pos p hp x hv)]
  change w x*(_*(_*secondNormProfile _ _ _ _ _
    (relativeNorm (coordinates p x) Z D B v θ H)))=0
  simp only [secondNormProfile,hW,mul_zero,zero_mul,zero_div]

include hp hcop hg in

theorem physical_nonzero_clipping
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Point ι→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂ ω₁ ω₂:ℝ→ℂ)(V:Fin 6→ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D B v θ H m c₁ c₂ θ₁ θ₂ a b η:ℝ)(hZ:1<Z)(hb:1≤b)
    (hω:Function.support ω₁⊆Set.Icc a b)
    (hs:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
    (ht:Real.log b≤3*η*Real.log Z)
    (hn:physicalBlock p hp hcop hg (pointSource pool S) w Ψ j marks
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m≠0) :
    0≤max 0 (columnCenter D B v)-columnCenter D B v ∧
      max 0 (columnCenter D B v)-columnCenter D B v≤3*η := by
  apply freshColumns_initial_clipping_shift p hp pool ω₁ a b Z (columnCenter D B v) η hZ hb hω _ ht
  by_contra he
  have he':freshColumns p pool ω₁ (Z^(columnCenter D B v))=∅:=Finset.not_nonempty_iff_eq_empty.mp he
  exact hn (physicalBlock_zero_of_fresh_empty p hp hcop hg hpr pool S hdiv hf w Ψ j marks
    W₁ W₂ ω₁ ω₂ V Φ Z D B v θ H m c₁ c₂ θ₁ θ₂ (zero_lt_one.trans hZ) hs he')

end SevenEighths.InverseInitialEnergyCallerEmpty

end

end OAI
