import OAI.NumberTheory.DirichletL.Inversion.InitialZeroMode

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialZeroMode
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT EisensteinSchwartzPoisson InverseMoment
open InverseInitialRayAttachment FirstCauchyArithmetic
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,λ₀∉Ideal.span {p i})(hinj:Function.Injective (fun i=>Ideal.span {p i}))
  (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,λ₀^2∣p i-1)

include hinj hc hpr

theorem physical_zero_off_diagonal
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G U T E:Finset ι)(hGU:Disjoint G U)(hGT:Disjoint G T)(hUT:Disjoint U T)(hne:U≠T):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0=0 := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G U T E hGU hGT hUT 0,
    activeGaussRowFactor_zero_of_ne p hp hg hinj T U hne.symm]
  simp

theorem physical_zero_empty
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (G E:Finset ι):
    initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0=
    ((Z^(-D):ℝ):ℂ)*(Z^m:ℝ)*paperRadialFourier Φ 0*
      ((‖secondInputCoefficient p hg Ψ j 1 1 (fun _=>1) G‖^2:ℝ):ℂ)*
      star (initialTest p σ W Z D G)*initialTest p σ W Z D G*
      ((UniqueFactorizationMonoid.moebius (∏i∈E,Ideal.span {p i}):ℂ)/
        (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)‖^2:ℝ)) := by
  rw [←normalized_overlap_mode p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m
    G ∅ ∅ E (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) (Finset.disjoint_empty_left _) 0,
    activeGaussRowFactor_empty (p := p) (hp := hp) (hg := hg) (hinj := hinj)]
  have hcoef (H:Finset ι→ℂ):secondInputCoefficient p hg Ψ j 1 1 H ∅=H ∅:=by
    simp [secondInputCoefficient,rowCoprimeMask,finiteSquarefreeRow]
  have hμ:supportMobius (fun i=>Ideal.span {p i}) ∅=(1:ℂ):=by
    change (UniqueFactorizationMonoid.moebius (1:Ideal O):ℂ)=1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [overlapPairWeight,hcoef,hμ,one_mul,Finset.union_empty]
  have hempty:activeSupport (∅:Finset ι) ∅=∅:=by simp [activeSupport]
  let:IsEmpty (activeSupport (∅:Finset ι) ∅):=⟨fun ⟨x,hx⟩=>by
    simp only [activeSupport,Finset.sdiff_self,Finset.union_self,Finset.notMem_empty] at hx⟩
  simp only [Fintype.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
    zero_pow (by decide:2≠0),mul_zero,zero_div,mul_one]
  ring

theorem physical_zero_sum
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E 0 else 0)=
      ((Z^(-D):ℝ):ℂ)*truncatedSecondZero p hg pool Ψ j 1 1
        (initialTest p σ W Z D) Φ (Z^m) (fun _ _=>{0}) := by
  unfold truncatedSecondZero
  simp only [Finset.mem_singleton,ite_true,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp only [Finset.disjoint_empty_left,ite_true]
      rw [←Finset.sum_coe_sort (s:=G.powerset) (f:=fun E=>
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G ∅ ∅ E 0)]
      apply Finset.sum_congr rfl
      intro E hE
      rw [physical_zero_empty p hp hcop hg hinj hc hpr]
      ring
    · intro T hT hne
      simp only [Finset.disjoint_empty_left,ite_true]
      apply Finset.sum_eq_zero
      intro E hE
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G ∅ T E
        (Finset.disjoint_empty_right _) (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff)
        (Finset.disjoint_empty_left _) hne.symm
    · simp
  · intro U hU hne
    apply Finset.sum_eq_zero
    intro T hT
    split_ifs with hUT
    · apply Finset.sum_eq_zero
      intro E hE
      have hneq:U≠T:=by
        intro he
        subst T
        exact hne (by simpa using Finset.disjoint_iff_inter_eq_empty.mp hUT)
      exact physical_zero_off_diagonal p hp hcop hg hinj hc hpr Ψ j σ W Φ Z D m G U T E
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
        (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hUT hneq
    · rfl
  · simp

end SevenEighths.InverseInitialZeroMode

end

end OAI
