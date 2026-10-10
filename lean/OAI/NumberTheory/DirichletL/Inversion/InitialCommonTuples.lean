import OAI.NumberTheory.DirichletL.Inversion.InitialCommonForcing

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ConcretePrimeRowBridge
open FirstCauchyArithmetic SecondPassArithmetic
namespace SevenEighths.InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialRayAttachment InverseInitialArithmetic InverseInitialCommonPool
open InverseInitialEnergyCallerWindow InverseInitialCommonForcing
local notation "Eis"=>ActualEisensteinCubic.O
variable {κ ι : Type*} [DecidableEq ι]

theorem input_finset_sum (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,goodLambda∉Ideal.span {p i})(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (T:Finset κ)(a:κ→ℂ)(H:κ→Finset ι→ℂ) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∑k∈T,a k*H k A) u=
      ∑k∈T,a k*inputConjugateRow p hg F Ψ j 1 1 (H k) u := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro A hA
  ring

def tupleColumns (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis) :
    Finset (Ideal Eis) := T.biUnion (fun k=>columns S (P k) j)

theorem tupleColumns_admissible (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hS:∀n∈S,Squarefree n→Supported n) :
    ∀c∈tupleColumns S T P j,Admissible c := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact columns_admissible S (hP k hk) (hj k hk) hS hc

theorem tupleColumns_coprime (S:Finset (Ideal Eis))(T:Finset κ)(P:κ→Ideal Eis)
    (j:Ideal Eis)(hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k) :
    ∀c∈tupleColumns S T P j,IsCoprime c j := by
  intro c hc
  obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
  exact ((mem_columns (hP k hk).2.1 (hj k hk)).mp hc).2.1

theorem original_tuples_common_input
    (W:ℝ→ℂ)(Z r z G b:ℝ)(hZ:0<Z)(hW:∀x,W x≠0→x≤b)
    (T:Finset κ)(P:κ→Ideal Eis)(j:Ideal Eis)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (η:Ideal Eis→*ℂ)(a:κ→ℂ)(u:Eis) :
    let S := originalSource Z r b
    let F := tupleColumns S T P j
    let hF := tupleColumns_admissible S T P j hP hj (originalSource_supported Z r b)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑k∈T,a k*residualNormalizedPolynomial S (P k) j η (fun _=>1) W Z r z G u)=
      ((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
        (poolPrimary F) (poolPrimary_good F hF) Finset.univ
        (elementCharacter η) (primaryGenerator j) 1 1
        (fun A=>∑k∈T,a k*(if residual (P k) j∣(∏i∈A,i.val) then
          residualOverlapWindow (P k) j W Z z G
            (((∏i∈A,i.val).absNorm:ℝ)/Z^(r+z-2*G)) else 0)) u := by
  intro S F hF
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  erw [input_finset_sum (p := poolPrimary F)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [residual_eq_common_forcing W Z r z G b hZ hW (hP k hk) (hj k hk) F hF
    (tupleColumns_coprime S T P j hP hj)
    (fun c hc=>Finset.mem_biUnion.mpr ⟨k,hk,hc⟩) η u]
  ring

end SevenEighths.InverseInitialCommonTuples

end

end OAI
