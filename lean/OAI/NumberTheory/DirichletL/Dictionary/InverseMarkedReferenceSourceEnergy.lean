import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceMass
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceArithmetic
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
import OAI.NumberTheory.DirichletL.Inversion.InitialResidualUniformEnergy
import OAI.NumberTheory.DirichletL.Inversion.InitialMarkedAssignedGeometry
import OAI.NumberTheory.DirichletL.Inversion.InitialMarkedReserve
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
local notation "O"=>HeckeFamily.O

private theorem assigned_admissible {ι:Type}[Fintype ι][DecidableEq ι]
    (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J):Admissible (assignedIdeal L J x) := by
  apply tuple_admissible (fun i:↥J=>L i.val)
    (fun i=>hp i.val) (fun i=>hs i.val) _ x
  intro i hi j hj hij
  exact hdis (Finset.mem_univ _) (Finset.mem_univ _)
    (fun he=>hij (Subtype.ext he))

theorem original_source_energy
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (gap eps π eta τ loss:ℝ)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hetagap:eta≤gap/50)
    (hτ:0<τ)(hτgap:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∀q:ℕ,q≠0→∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      r+2*(∑i,ell i)≤m-2*gap→2*r+8*(∑i,ell i)≤3*m-2*gap→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  obtain ⟨degree,henergy⟩:=InverseInitialResidualUniformEnergy.original_residual_uniform_energy
    (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
    DetectorDictionaryInverseMarkedPadding.radialMajorant
    DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
    DetectorDictionaryInverseMarkedPadding.radialMajorant_one
    2 gap eps π eta τ loss (by norm_num) hgap heps hπ heta hetaone hetagap hτ hτgap hloss K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero m r hm hmcap hD hfirst hsecond hparent rows hrows θ
  have hUone:1<U:=hU₀.trans_le hU
  have hUpos:0<U:=zero_lt_one.trans hUone
  have hscale (i:ι):0<U^(ell i):=Real.rpow_pos_of_pos hUpos _
  have hnorm (i:ι)(P:Ideal O)(hP:P∈L i):(P.absNorm:ℝ)≤2*U^(ell i):=
    (div_le_iff₀ (hscale i)).mp (hratio i P hP).2
  let E:ℝ:=C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2
  have hE:0≤E:=by dsimp [E];positivity
  have hres (J:Finset ι)(x:Assigned L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomial (originalSource U r bo) L J x coeff χ
        (childLogTest W θ) U r (∑i,ell i) (∑i∈J,ell i) u‖^2)≤E := by
    have hJ:J.card≤K:=(Finset.card_le_univ J).trans hK
    have hH (i:ι):1≤2*U^(ell i) := by
      have hh:=Real.one_le_rpow hUone.le (hell i)
      linarith
    have hprod (T:Finset ι):
        (∏i∈T,2*U^(ell i))≤U^((∑i∈T,ell i)+eta) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUpos,
        Real.rpow_add hUpos]
      rw [mul_comm (U^(∑i∈T,ell i))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
      exact (pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ T).trans hK)).trans hpow
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible L hp hs hdis J x
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P)) hdis
      (fun i _=>hH i) (fun i _=>hnorm i)
      (fun i _ P hP=>by simpa using hc i P hP)
      (assignedGenerator L J x) ell (fun _=>1) (fun _=>2) primeW
      (fun i _=>hell i)
      (assignedGenerator_ne_zero L J x (fun i _ P hP=>(hp i P hP).ne_zero))
      (fun i _=>hprimeW i) (assignedGenerator_window_live L J x U ell primeW (fun i _=>hlive i))
      (conjugateIdealCharacter χ)
      (fun u=>by simpa [elementCharacter,conjugateIdealCharacter] using hχ (Ideal.span {u}))
      hperiod hzero (r+(∑i,ell i)-2*(∑i∈J,ell i)) m r hm hmcap (hD J)
      (by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ).trans hpow)
      (by simpa [assignedCenter] using hprod (Finset.univ\J))
      rfl (by simpa [assignedCenter] using hfirst) (by simpa [assignedCenter] using hsecond)
      (by simpa [assignedCenter] using hparent) rows hrows (assignedIdeal L J x) hje
      (assignedElement_span L J x)
      (assigned_ratio_interval L J x U hUpos ell K hJ (fun i _=>hratio i))
      (fun i _=>hp i) (fun i _ P hP _=>hratio i P hP)
      (remaining_tuple_admissible L hp hs hdis J x)
      (remaining_tuple_coprime L hp hdis J)
      (remaining_tuple_outside L (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
        hout J x) (-θ)
    simpa only [one_mul,remainingPolynomial_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp hdis ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (assigned_admissible L hp hs hdis) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
