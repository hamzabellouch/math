import Mathlib
import OAI.Algebra.GroupRing.PictureChains
import OAI.Algebra.GroupRing.GraphConePresentation

namespace OAI



section
namespace TorsionFreeZeroDivisors.ConeChains
open PortSubdivision GraphPresentation GraphConePresentation
open scoped Classical BigOperators
noncomputable section
variable {V D A S : Type} (Γ : PortGraph V D) (R : Routes Γ)
  (label : D→A) (inv : A→A) (letters : A→FreeGroup S)
  (hi : Function.Involutive inv) (hl : ∀d,label (Γ.reverse d)=inv (label d))
  (hw : ∀a,letters (inv a)=(letters a)⁻¹)
local notation "G" => GraphConePresentation.Group Γ (letters ∘ label) R
abbrev Cells := G × Edge Γ
abbrev TwoChain := Cells Γ R label letters →₀ ℤ
lemma edge_reverse (d : D) : edge Γ (Γ.reverse d)=edge Γ d :=
  Quotient.sound (Or.inr rfl)
lemma representative_edge (e : Edge Γ) : edge Γ (representative Γ e)=e := Quotient.out_eq e
include hl hw in
lemma letters_reverse (d : D) : (letters ∘ label) (Γ.reverse d)=((letters ∘ label) d)⁻¹ := by
  simp only [Function.comp_apply,hl,hw]
def eval : A ⊕ (ConePicture.Radial Γ R × Bool)→G
  | .inl a => oldMap Γ (letters ∘ label) R (letters a)
  | .inr (v,b) => if b then radialValue Γ (letters ∘ label) R v else (radialValue Γ (letters ∘ label) R v)⁻¹
include hw in
lemma eval_inverse (a : A ⊕ (ConePicture.Radial Γ R × Bool)) :
    eval Γ R label letters (ConePicture.inverse Γ R inv a)=(eval Γ R label letters a)⁻¹ := by
  rcases a with a|⟨v,b⟩
  · simp only [ConePicture.inverse,eval,hw,map_inv]
  · cases b <;> simp [ConePicture.inverse,eval]
/-- Actual oriented physical two-cell with its group translate. The translation
is measured from the common cone apex, not from the endpoint of the edge. -/
def cell (g : G) (d : D) : Cells Γ R label letters :=
  (g*(radialValue Γ (letters ∘ label) R (Γ.origin d))⁻¹,edge Γ d)
include hl hw in
lemma cell_reverse (g : G) (d : D) :
    cell Γ R label letters (g*oldMap Γ (letters ∘ label) R (letters (label d))) (Γ.reverse d)=
      cell Γ R label letters g d := by
  apply Prod.ext
  · dsimp [cell]
    rw [edge_value Γ (letters ∘ label) R (letters_reverse Γ label inv letters hl hw)]
    dsimp only [Function.comp_apply]
    group
  · exact edge_reverse Γ d

def charge (g : G) (d : D) : TwoChain Γ R label letters :=
  if d=representative Γ (edge Γ d) then Finsupp.single (cell Γ R label letters g d) 1
  else -Finsupp.single (cell Γ R label letters g d) 1
include hl hw in
lemma charge_reverse (g : G) (d : D) :
    charge Γ R label letters (g*oldMap Γ (letters ∘ label) R (letters (label d))) (Γ.reverse d)=
      -charge Γ R label letters g d := by
  rw [charge,cell_reverse Γ R label inv letters hl hw,edge_reverse]
  by_cases hd : d=representative Γ (edge Γ d)
  · have hr : Γ.reverse d≠representative Γ (edge Γ d) := by
      rw [←hd];exact Γ.reverse_ne d
    rw [ite_eq_right hr,charge,ite_eq_left hd]
  · have hr : Γ.reverse d=representative Γ (edge Γ d) := by
      rcases representative_cases Γ d with hh|hh
      · exact (hd hh).elim
      · exact (congrArg Γ.reverse hh).trans (Γ.reverse_reverse_apply _)
    rw [ite_eq_left hr,charge,ite_eq_right hd,neg_neg]
def coneCharge (g : G) : ConePicture.Dart Γ R→TwoChain Γ R label letters
  | .inl d => charge Γ R label letters g d
  | .inr _ => 0
include hl hw in
lemma coneCharge_reverse (g : G) (d : ConePicture.Dart Γ R) :
    coneCharge Γ R label letters
      (g*eval Γ R label letters (ConePicture.labels Γ R label d)) ((ConePicture.graph Γ R).reverse d)=
    -coneCharge Γ R label letters g d := by
  rcases d with d|p
  · exact charge_reverse Γ R label inv letters hl hw g d
  · exact (neg_zero).symm

variable {O : Type} [Fintype O]
  (a : SphericalPicture.Data (O:=O) (ConePicture.graph Γ R)
    (ConePicture.labels Γ R label) (ConePicture.inverse Γ R inv))
  (l : PictureChains.Lift _ _ _ (eval Γ R label letters) a)
include hi hl hw in
/-- Sharp arrangement exclusion annihilates the genuine free integral
physical-cell charge of every lifted cone boundary picture. -/
theorem chain_zero
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (b : SphericalPicture.Data (O:=P) Γ label inv),¬b.Reduced) :
    (∑i,coneCharge Γ R label letters (l.position i) (a.dart i))=0 :=
  PictureChains.chain_eq_zero (eval_inverse Γ R label inv letters hw)
    (ConePicture.label_reverse Γ R label inv hl) a l (coneCharge Γ R label letters)
    (coneCharge_reverse Γ R label inv letters hl hw)
    (ConePicture.reduces_to_empty a hi hl hex)
end
end TorsionFreeZeroDivisors.ConeChains

end


end OAI
