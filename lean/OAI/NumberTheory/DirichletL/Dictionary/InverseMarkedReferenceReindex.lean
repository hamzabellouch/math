import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceRemaining

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialPoissonBridge InverseInitialConjugateEnergy InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingIndexEquiv (J:Finset ι) : {i:ι // i∉J} ≃ ↥(Finset.univ\J) where
  toFun i:=⟨i.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  invFun i:=⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem remaining_product_attach {A:Type*}[CommMonoid A]
    (J:Finset ι)(f:{i:ι // i∉J}→A) :
    (∏i,f i)=∏i∈(Finset.univ\J).attach,f ⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩ := by
  exact ((remainingIndexEquiv J).symm.prod_comp f).symm

def remainingPi (L:ι→Finset (Ideal O))(J:Finset ι)(q:Remaining L J) :
    ∀i∈Finset.univ\J,Ideal O := fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).val

theorem sum_remaining_original (L:ι→Finset (Ideal O))(J:Finset ι)
    (f:(∀i∈Finset.univ\J,Ideal O)→ℂ) :
    (∑q:Remaining L J,f (remainingPi L J q))=∑q∈(Finset.univ\J).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp hq i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he ⟨i,(Finset.mem_sdiff.mp hi).2⟩)
  · intro q hq
    refine ⟨remainingPi L J q,Finset.mem_pi.mpr (fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_original_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ\J).pi L,(∏i∈(Finset.univ\J).attach,star (coeff i.val (q i.val i.property)))*
        residualNormalizedPolynomial S (assignedIdeal L J x*survivingProduct (Finset.univ\J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_remaining_original]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  unfold remainingIdeal survivingProduct remainingPi
  rw [remaining_product_attach J (fun i=>star (coeff i.val (q i).val)),
    remaining_product_attach J (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
