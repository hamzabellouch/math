import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.EnergyLaurentSeries
import OAI.Combinatorics.Chromatic.Shuffle.InputTorusEnergy

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable

lemma card_fibres_injective_regrade {X Y : Type*} (f : X → ℤ) (g : Y → ℤ)
    (n : ℤ → ℤ) (hn : Function.Injective n)
    (h : ∀ k,Nat.card {x : X // f x=k}=Nat.card {y : Y // g y=k}) (e : ℤ) :
    Nat.card {x : X // n (f x)=e}=Nat.card {y : Y // n (g y)=e} := by
  by_cases H : ∃ k,n k=e
  · obtain ⟨k,hk⟩:=H
    let ex : {x : X // n (f x)=e} ≃ {x : X // f x=k} :=
      Equiv.subtypeEquivRight (fun x=>by rw [←hk,hn.eq_iff])
    let ey : {y : Y // n (g y)=e} ≃ {y : Y // g y=k} :=
      Equiv.subtypeEquivRight (fun y=>by rw [←hk,hn.eq_iff])
    rw [Nat.card_congr ex,Nat.card_congr ey]
    exact h k
  · let : IsEmpty {x : X // n (f x)=e} := ⟨fun x=>H ⟨f x.val,x.property⟩⟩
    let : IsEmpty {y : Y // n (g y)=e} := ⟨fun y=>H ⟨g y.val,y.property⟩⟩
    simp

universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance energySlopeSymmetricFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

noncomputable def stringBlockEnergy (d : I → ℕ) (i : StringBlockIndex a c η hc d) : ℤ :=
  (i.2.2.val.val.map (fun j=>stringStartParameter a κ c η hc (slope c η d) j-2*j.2.1)).sum

lemma stringBlockEnergy_normalized (d : I → ℕ) (i : StringBlockIndex a c η hc d) :
    stringBlockEnergy a κ c η hc d i=normalizedEnergy a κ d i.1 := by
  have H:=stringWordEnergy a κ c η hc (slope c η d) i.2.2.val
  rw [i.2.2.property] at H
  exact H.symm

noncomputable def hnStringEnergy : (l : List (I → ℕ)) → HNStringIndex a c η hc l → ℤ
  | [],_ => 0
  | d::l,i => stringBlockEnergy a κ c η hc d i.1+hnStringEnergy l i.2+
      (eulerForm a d l.sum-eulerForm a l.sum d)

lemma hnStringEnergy_normalized (l : List (I → ℕ)) (i : HNStringIndex a c η hc l) :
    hnStringEnergy a κ c η hc l i=normalizedEnergy a κ l.sum (hnStringDegree a c η hc l i) := by
  induction l with
  | nil => simp [hnStringEnergy,hnStringDegree,normalizedEnergy,eulerForm]
  | cons d l ih =>
    rcases i with ⟨i,j⟩
    change stringBlockEnergy a κ c η hc d i+hnStringEnergy a κ c η hc l j+
      (eulerForm a d l.sum-eulerForm a l.sum d)=_
    rw [stringBlockEnergy_normalized,ih]
    exact (normalizedEnergy_product a κ d l.sum i.1 (hnStringDegree a c η hc l j)).symm

omit [DecidableEq I] in
lemma normalizedEnergy_injective (d : I → ℕ) : Function.Injective (normalizedEnergy a κ d) := by
  intro x y h
  unfold normalizedEnergy at h
  omega

abbrev OutputEnergyCoefficient (d : I → ℕ) (e : ℤ) :=
  {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val // hnStringEnergy a κ c η hc i.1.val i.2=e}

theorem finiteReordering_energyCoefficient (ε : I → Bool)
    (ha : ∀ i,a i i=elementaryDiagonal ε i) (d : I → ℕ) (e : ℤ) :
    Nat.card {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e}=
      Nat.card (OutputEnergyCoefficient a κ c η hc d e) := by
  let ex : {x : SortedPackExponent d // normalizedEnergy a κ d (sortedPackDegree d x)=e} ≃
      {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e} :=
    (inputListEquiv ε d).subtypeEquiv (by intro x; rw [inputListEnergy_normalized a κ ε d ha])
  let ey : OutputEnergyCoefficient a κ c η hc d e ≃
      {i : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
        normalizedEnergy a κ d (hnStringDegree a c η hc i.1.val i.2)=e} :=
    Equiv.subtypeEquivRight (by
      intro i
      rw [hnStringEnergy_normalized,i.1.property.1])
  rw [←Nat.card_congr ex,Nat.card_congr ey]
  exact card_fibres_injective_regrade _ _ _ (normalizedEnergy_injective a κ d)
    (finiteStringReordering_coefficient a c η hc d) e
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open ElementaryPositivity.SlopeArithmetic
attribute [local instance] Classical.propDecidable
universe u

lemma finite_injective_regrade {X : Type*} (f : X → ℤ)
    (hf : ∀k,Finite {x : X // f x=k}) (n : ℤ → ℤ)
    (hn : Function.Injective n) (e : ℤ) : Finite {x : X // n (f x)=e} := by
  classical
  by_cases H : ∃k,n k=e
  · obtain ⟨k,hk⟩:=H
    let := hf k
    let E : {x : X // n (f x)=e} ≃ {x : X // f x=k} :=
      Equiv.subtypeEquivRight (fun _=>by rw [←hk,hn.eq_iff])
    exact Finite.of_equiv _ E.symm
  · let : IsEmpty {x : X // n (f x)=e} := ⟨fun x=>H ⟨f x.val,x.property⟩⟩
    infer_instance

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ) (c η : I → ℝ) (hc : ∀ i,0<c i)
  [hχ : Fact (∀ θ,SlopeEulerSymmetric a c η θ)]
local instance finiteLaurentSlopeFact (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩

omit [DecidableEq I] in
lemma sortedPackDegree_finite (d : I → ℕ) (k : ℤ) :
    Finite {i : SortedPackExponent d // (sortedPackDegree d i : ℤ)=k} := by
  let := componentS_range_finite d k
  exact ElementaryPositivity.homogeneousBasis_finite (packOrbitBasis d)
    (fun i=>(sortedPackDegree d i:ℤ)) (componentS d) (packOrbitBasis_component d) k

omit [DecidableEq I] in
lemma inputEnergy_admissible (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    EnergyLaurent.Admissible (inputTorusEnergy a κ ε d) := by
  have he (x : InputIndexLists ε d) : inputTorusEnergy a κ ε d x=
      normalizedEnergy a κ d (sortedPackDegree d ((inputListEquiv ε d).symm x)) := by
    simpa using inputListEnergy_normalized a κ ε d ha ((inputListEquiv ε d).symm x)
  constructor
  · refine ⟨inputShift a κ d-eulerForm a d d,fun x=>?_⟩
    rw [he]
    unfold normalizedEnergy
    have H : 0≤(sortedPackDegree d ((inputListEquiv ε d).symm x):ℤ) := by positivity
    omega
  · intro e
    let E : {x : SortedPackExponent d // normalizedEnergy a κ d (sortedPackDegree d x)=e} ≃
        {x : InputIndexLists ε d // inputTorusEnergy a κ ε d x=e} :=
      (inputListEquiv ε d).subtypeEquiv (by intro x; rw [inputListEnergy_normalized a κ ε d ha])
    let := finite_injective_regrade (fun x : SortedPackExponent d=>(sortedPackDegree d x:ℤ))
      (sortedPackDegree_finite d) (normalizedEnergy a κ d) (normalizedEnergy_injective a κ d) e
    exact Finite.of_equiv _ E

lemma hnStringDegree_nonneg (d : I → ℕ)
    (x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val) :
    0≤hnStringDegree a c η hc x.1.val x.2 := by
  by_contra H
  let k := hnStringDegree a c η hc x.1.val x.2
  have hk : k<0 := lt_of_not_ge H
  let : IsEmpty {i : SortedPackExponent d // (sortedPackDegree d i:ℤ)=k} :=
    ⟨fun i=>by
      have hi:=i.property
      have hn : 0≤(sortedPackDegree d i.val:ℤ) := Int.natCast_nonneg _
      omega⟩
  let := hnStringCoefficient_finite a c η hc d k
  let : Nonempty (HNStringCoefficient a c η hc d k) := ⟨⟨x,rfl⟩⟩
  have hpos : 0<Nat.card (HNStringCoefficient a c η hc d k) := Nat.card_pos
  have he := finiteStringReordering_coefficient a c η hc d k
  simp only [Nat.card_of_isEmpty] at he
  omega

lemma outputEnergy_admissible (d : I → ℕ) :
    EnergyLaurent.Admissible (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
      hnStringEnergy a κ c η hc x.1.val x.2) := by
  constructor
  · refine ⟨inputShift a κ d-eulerForm a d d,fun x=>?_⟩
    dsimp only
    rw [hnStringEnergy_normalized,x.1.property.1]
    have H:=hnStringDegree_nonneg a c η hc d x
    unfold normalizedEnergy
    omega
  · intro e
    let := finite_injective_regrade
      (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
        hnStringDegree a c η hc x.1.val x.2)
      (hnStringCoefficient_finite a c η hc d) (normalizedEnergy a κ d)
      (normalizedEnergy_injective a κ d) e
    let E : OutputEnergyCoefficient a κ c η hc d e ≃
        {x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val //
          normalizedEnergy a κ d (hnStringDegree a c η hc x.1.val x.2)=e} :=
      Equiv.subtypeEquivRight (fun x=>by rw [hnStringEnergy_normalized,x.1.property.1])
    exact Finite.of_equiv _ E.symm

noncomputable def inputReorderingSeries (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) : LaurentSeries ℚ :=
  EnergyLaurent.series (inputTorusEnergy a κ ε d) (inputEnergy_admissible a κ ε ha d)

noncomputable def outputReorderingSeries (d : I → ℕ) : LaurentSeries ℚ :=
  EnergyLaurent.series
    (fun x : Σ l : HNIndex c η d,HNStringIndex a c η hc l.val=>
      hnStringEnergy a κ c η hc x.1.val x.2)
    (outputEnergy_admissible a κ c η hc d)

theorem finiteReordering_laurent (ε : I → Bool)
    (ha : ∀i,a i i=elementaryDiagonal ε i) (d : I → ℕ) :
    inputReorderingSeries a κ ε ha d=outputReorderingSeries a κ c η hc d := by
  apply EnergyLaurent.series_eq_of_cards
  exact finiteReordering_energyCoefficient a κ c η hc ε ha d

end ElementaryPositivity.RawShuffle

end

end OAI
