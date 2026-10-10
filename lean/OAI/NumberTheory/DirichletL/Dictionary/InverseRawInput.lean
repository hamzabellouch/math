import OAI.NumberTheory.DirichletL.Dictionary.InverseRawConjugateGates
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedForcing

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseRawInput
open CompletedGauss
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ConcreteTraceCRT FirstCauchyArithmetic SecondPassArithmetic IdealMobiusDivisorSum
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialConjugateEnergy
open InverseInitialPoissonBridge InverseInitialExcludedForcing InverseInitialExcludedPool
open UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

private theorem admissible_one : Admissible (1:Ideal O):=by
  refine ⟨one_ne_zero,squarefree_one,?_⟩
  simp only [normalizedFactors_one,Multiset.notMem_zero,false_implies,forall_const]

theorem input_generator_one (F:Finset (Ideal O))(hF:∀I∈F,Admissible I)
    (η:O→*ℂ)(H:Finset (primePool F)→ℂ)(u:O):
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η
      (primaryGenerator (1:Ideal O)) 1 1 H u=
    inputConjugateRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ η 1 1 1 H u:=by
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  rw [initial_input_row (poolPrimary F) (poolPrimary_good F hF),
    initial_input_row (poolPrimary F) (poolPrimary_good F hF)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  have he:(fun i:primePool F=>Ideal.span {poolPrimary F i})=(fun i=>i.val):=
    funext (poolPrimary_span F hF)
  have hm:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A
      (primaryGenerator (1:Ideal O))=1:=by
    rw [he]
    exact selected_mask F 1 admissible_one A isCoprime_one_right
  have ho:rowCoprimeMask (fun i:primePool F=>Ideal.span {poolPrimary F i}) A 1=1:=by
    simp [rowCoprimeMask,Ideal.IsPrime.one_notMem]
  simp only [hm,ho]

theorem complete_pool_selector (E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (Dpool:ℕ)(hbad:fixedBadPrimes⊆E)(W:ℝ→ℂ)(b Z r:ℝ)
    (hZ:0<Z)(hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ)):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    ∀A:Finset (primePool F),
      (if (∏i∈A,i.val)∈F then W (((∏i∈A,i.val).absNorm:ℝ)/Z^r) else 0)=
        W (((∏i∈A,i.val).absNorm:ℝ)/Z^r):=by
  intro F A
  by_cases hw:W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)=0
  · simp only [hw,ite_self]
  have hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad
  have hprod:=InitialMeanSquare.poolProduct_admissible F hF A
  have hout:outside E (∏i∈A,i.val):=
    pool_product_outside F E hE
      (fun I hI=>(mem_outsideIdealsUpTo.mp (Finset.mem_filter.mp hI).1).2.2) A
  have hN:((∏i∈A,i.val).absNorm:ℝ)≤(Dpool:ℝ):=
    ((div_le_iff₀ (Real.rpow_pos_of_pos hZ r)).mp (hW _ hw)).trans hbudget
  have hmem:(∏i∈A,i.val)∈F:=by
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,hout⟩,hprod.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprod.1)
    · exact_mod_cast hN
  exact ite_eq_left hmem

theorem original_complete_star_input
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    star (originalTotalPolynomial F 1 η (fun _=>1) W Z r 0 u)=
      ((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r) u:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have he:=selected_conjugate_row F hF 1 admissible_one (fun _ _=>isCoprime_one_right)
    (conjugateIdealCharacter η) (fun I=>star (W ((I.absNorm:ℝ)/Z^r))) u
  dsimp only at he
  rw [input_generator_one F hF] at he
  have hselector:(fun A:Finset (primePool F)=>
      if (∏i∈A,i.val)∈F then star (W (((∏i∈A,i.val).absNorm:ℝ)/Z^r)) else 0)=
      initialTest (poolPrimary F) (fun _=>1) (fun x=>star (W x)) Z r:=by
    funext A
    rw [complete_pool_selector E hE Dpool hbad (fun x=>star (W x)) b Z r hZ
      (fun x hx=>hW x (by simpa only [star_ne_zero] using hx)) hbudget]
    simp only [initialTest,one_mul,InitialMeanSquare.poolPrimary_norm F hF]
    rfl
  rw [hselector] at he
  rw [←he]
  unfold originalTotalPolynomial
  have hscalar:star ((Z^(-r/2):ℝ):ℂ)=((Z^(-r/2):ℝ):ℂ):=by simp
  simp only [add_zero,map_one,mul_one,star_mul,star_sum,hscalar,
    conjugateIdealCharacter_apply,heckeIdealCharacter_apply]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [star_intCast]
  ring

theorem original_complete_child_norm
    (E:Finset (Ideal O))(hE:∀P∈E,Prime P)(Dpool:ℕ)(hbad:fixedBadPrimes⊆E)
    (η:Ideal O→*ℂ)(W:ℝ→ℂ)(b Z r t:ℝ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤b)(hbudget:b*Z^r≤(Dpool:ℝ))(u:O):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals E Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible E Dpool hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    ‖originalTotalPolynomial F 1 η (fun _=>1) (InverseMoment.childLogTest W t) Z r 0 u‖^2=
      ‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ (elementCharacter (conjugateIdealCharacter η)) 1 1 1
        (initialTest (poolPrimary F) (fun _=>1)
          (InverseMoment.childLogTest (fun x=>star (W x)) (-t)) Z r) u‖^2:=by
  intro F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hw:∀x,InverseMoment.childLogTest W t x≠0→x≤b:=by
    intro x hx
    exact hW x ((mul_ne_zero_iff.mp hx).1)
  have he:=original_complete_star_input E hE Dpool hbad η
    (InverseMoment.childLogTest W t) b Z r hZ hw hbudget u
  dsimp only at he
  rw [DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate] at he
  have hn:=congrArg (fun z:ℂ=>‖z‖^2) he
  simpa only [norm_star] using hn

end SevenEighths.DetectorDictionaryInverseRawInput

end

end OAI
