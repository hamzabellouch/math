import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.EnergyLaurentSeries

namespace OAI

section
namespace ElementaryPositivity.EnergyLaurent
noncomputable section
variable {A : Type*} {e : A → ℤ}

lemma admissible_subtype (he : Admissible e) (p : A → Prop) :
    Admissible (fun x : {a // p a}=>e x.val) := by
  refine ⟨?_,?_⟩
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K,fun x=>hK x.val⟩
  · intro E
    let := he.2 E
    exact Finite.of_injective (fun x : {x : {a // p a} // e x.val=E}=>
      (⟨x.val.val,x.property⟩ : {a // e a=E}))
      (fun x y H=>Subtype.ext (Subtype.ext (congrArg (fun z : {a // e a=E}=>z.val) H)))

variable {J : Type*} [Fintype J] {B : J → Type*} (f : ∀j,B j → ℤ)

def sigmaEnergyFiber (E : ℤ) :
    {x : Σj,B j // f x.1 x.2=E} ≃ Σj,{x : B j // f j x=E} where
  toFun x:=⟨x.val.1,⟨x.val.2,x.property⟩⟩
  invFun x:=⟨⟨x.1,x.2.val⟩,x.2.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma admissible_sigma (hf : ∀j,Admissible (f j)) :
    Admissible (fun x : Σj,B j=>f x.1 x.2) := by
  classical
  constructor
  · let K : J → ℤ:=fun j=>Classical.choose (hf j).1
    refine ⟨∑j,|K j|,fun x=>?_⟩
    have H : f x.1 x.2≤K x.1 := Classical.choose_spec (hf x.1).1 x.2
    exact H.trans ((le_abs_self _).trans (Finset.single_le_sum (f:=fun j=>|K j|) (fun j _=>abs_nonneg (K j)) (Finset.mem_univ x.1)))
  · intro E
    let : ∀j,Finite {x : B j // f j x=E} := fun j=>(hf j).2 E
    exact Finite.of_equiv _ (sigmaEnergyFiber f E).symm

lemma series_sigma (hf : ∀j,Admissible (f j)) :
    series (fun x : Σj,B j=>f x.1 x.2) (admissible_sigma f hf)=∑j,series (f j) (hf j) := by
  classical
  ext j
  simp only [HahnSeries.coeff_sum,series_coeff]
  let : ∀i,Finite {x : B i // f i x= -j} := fun i=>(hf i).2 (-j)
  rw [Nat.card_congr (sigmaEnergyFiber f (-j)),Nat.card_sigma,Nat.cast_sum]

end
end ElementaryPositivity.EnergyLaurent

end

end OAI
