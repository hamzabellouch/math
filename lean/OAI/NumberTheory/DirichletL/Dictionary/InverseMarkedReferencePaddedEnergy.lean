import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceSourceEnergy

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure Filter
local notation "O"=>HeckeFamily.O

theorem padded_source_energy
    (W:ℝ → ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃eta:ℝ,0<eta ∧ ∃degree:ℕ,∀q:ℕ,q≠0 → ∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
    ∀(L:ι → Finset (Ideal O))(ell:ι → ℝ)(coeff:ι → Ideal O → ℂ),
      (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
      (∀i,∀P∈L i,Supported P) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L) →
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,‖coeff i P‖≤1) →
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P) →
    ∀(primeW:ι → ℝ → ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0) →
    ∀χ:Ideal O →*ℂ,(∀I,‖χ I‖≤1) →
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ)) →
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I →
        conjugateIdealCharacter χ I=0) →
    ∀r rr:ℝ,0≤r → r-eta≤rr → rr≤r →
      r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U rr bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U rr (∑i,ell i) u‖^2)≤
      C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨ρ,gap,eta,τ,π,eps,loss,hρ,hρmax,hρε,hgap,hgapρ,heta,hetamax,hetagap,
    hτ,hτgap,hπ,heps,hloss,hcost⟩:=InverseInitialMarkedReserve.exists_reserve εm hεm
  obtain ⟨degree,henergy⟩:=original_source_energy W ao bo hao hab hsW hW
    gap eps π eta τ loss hgap heps hπ heta (by linarith) hetagap hτ hτgap hloss K
  have hev:∀ᶠU:ℝ in atTop,(2:ℝ)^K≤U^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩:=eventually_atTop.mp hev
  refine ⟨eta,heta,degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  refine ⟨C,max U₀ Uscale,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero r rr hr hrlo hrhi hfirst hsecond rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hs0:0≤∑i,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hG (J:Finset ι):0≤∑i∈J,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hGmax (J:Finset ι):(∑i∈J,ell i)≤∑i,ell i:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)
  have hcap (J:Finset ι):
      0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤rr+(∑i,ell i)-2*(∑i∈J,ell i) ∧
      rr+2*(∑i,ell i)≤1+ρ-2*gap ∧
      2*rr+8*(∑i,ell i)≤3*(1+ρ)-2*gap ∧ rr+(∑i,ell i)+7*eta≤2 :=
    InverseInitialMarkedReserve.shifted_capacity ρ gap eta r rr _ _ hρ hρmax hgapρ
      heta hetamax hr hs0 (hG J) (hGmax J) hrlo hrhi hfirst hsecond
  have hbase:=hcap ∅
  have hrows':∀u∈rows,‖eisEmbedding u‖^2≤U^(1+ρ) := by
    intro u hu
    refine (hrows u hu).trans ?_
    calc U=U^(1:ℝ):=(Real.rpow_one U).symm
         _≤U^(1+ρ):=Real.rpow_le_rpow_of_exponent_le hUone.le (by linarith)
  have hh:=henergy U hU0 (hscale U ((le_max_right _ _).trans hU)) hK L ell coeff hell hp hs
    hdis hratio hc hout primeW hprimeW hlive χ hχ hperiod hzero (1+ρ) rr
    hbase.1 hbase.2.1 (fun J=>(hcap J).2.2.1) hbase.2.2.2.1 hbase.2.2.2.2.1
    hbase.2.2.2.2.2 rows hrows' θ
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hUone.le
  linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
