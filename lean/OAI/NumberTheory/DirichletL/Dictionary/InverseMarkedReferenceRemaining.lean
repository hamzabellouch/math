import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceOverlap
import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedFourier

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open InverseInitialOverlap UniqueFactorizationMonoid ActualEisensteinCubic
open InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem remaining_injective (L:ι→Finset (Ideal O))
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) : Function.Injective (fun i=>(y i).val) := by
  intro i j he
  apply Subtype.ext
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val) hij)
    (y i).property (by simpa only [he] using (y j).property)

theorem remaining_moebius (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(y:Remaining L J) :
    (moebius (remainingIdeal L J y):ℂ)=(-1:ℂ)^Fintype.card {i:ι // i∉J} := by
  let:∀i:{i:ι // i∉J},((y i).val).IsMaximal:=fun i=>
    (Ideal.isPrime_of_prime (hprime i.val _ (y i).property)).isMaximal
      (hprime i.val _ (y i).property).ne_zero
  simpa only [remainingIdeal,Finset.card_univ] using prime_product_moebius
    (fun i=>(y i).val) (fun i=>hprime i.val _ (y i).property)
    (remaining_injective L hdis J y) Finset.univ

def remainingPolynomial (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  ∑y:Remaining L J,(∏i:{i:ι // i∉J},star (coeff i.val (y i).val))*
    residualNormalizedPolynomial S (assignedIdeal L J x*remainingIdeal L J y)
      (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
      (fun v=>star (W v)) Z r z G u

theorem remainingResidual_eq_polynomial (S:Finset (Ideal O))
    (L:ι→Finset (Ideal O))(hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingResidual S L J x coeff η (fun _=>1) W Z r z G u=
      (-1:ℂ)^Fintype.card {i:ι // i∉J}*
      remainingPolynomial S L J x coeff η W Z r z G u := by
  unfold remainingResidual remainingPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [remaining_moebius L hprime hdis]
  simp only [star_mul,star_prod,star_pow,star_neg,star_one,conjugatedResidual]
  ring

theorem sum_tuple_pi (L:ι→Finset (Ideal O))
    (f:(∀i∈(Finset.univ:Finset ι),Ideal O)→ℂ) :
    (∑q:Tuple L,f (fun i _=>(q i).val))=
      ∑q∈(Finset.univ:Finset ι).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i (Finset.mem_univ i),
    Finset.mem_pi.mp hq i (Finset.mem_univ i)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i _=>(q i).val,Finset.mem_pi.mpr (fun i hi=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ:Finset {i:ι // i∉J}).pi (fun i=>L i.val),
        (∏i∈(Finset.univ:Finset {i:ι // i∉J}).attach,
          star (coeff i.val.val (q i.val i.property)))*
        residualNormalizedPolynomial S
          (assignedIdeal L J x*survivingProduct Finset.univ q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_tuple_pi]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  simp only [survivingProduct,remainingIdeal]
  rw [Finset.prod_attach _ (fun i=>star (coeff i.val (q i).val)),
    Finset.prod_attach _ (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
