import Mathlib
import OAI.Combinatorics.Chromatic.Witness.ElementarySingletonCoefficient
import OAI.Combinatorics.Chromatic.Witness.GraphRequiredPackets
import OAI.Combinatorics.Chromatic.Histories.PacketSortedWords

namespace OAI

section
namespace ElementaryPositivity
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
lemma sum_subtype_ite {A R:Type*} [Fintype A] [AddCommMonoid R] (P:A → Prop) [DecidablePred P] (f:A → R) :
    (∑a:{a // P a},f a.val)=∑a,if P a then f a else 0 := by
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm
end
namespace TriangularDynamics
open Packets
open WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

abbrev DecoratedLeaf:=Σl:HistoryLeaf G,
  LaurentPositive.Decoration (historyWeight G l) (historyWeight_positive G l) G.edgeCount

def leafEnergy (d:DecoratedLeaf G):ℕ:=d.2.1.val
abbrev DecoratedWord:=Σd:DecoratedLeaf G,AnchorWord (n:=n) (historyProfile G d.1)
def decoratedMask (w:DecoratedWord G):Finset (Fin (n-1)):=ascentMask (·<·) w.2.val
def decoratedEnergy (w:DecoratedWord G):ℕ:=leafEnergy G w.1
abbrev RequiredDecorated (J:Finset (Fin (n-1))):={w:DecoratedWord G // J⊆decoratedMask G w}

def requiredDecoratedEquiv (J:Finset (Fin (n-1))) : RequiredDecorated G J ≃
    Σd:DecoratedLeaf G,RequiredAnchor (n:=n) (historyProfile G d.1) J where
  toFun w:=⟨w.val.1,⟨w.val.2.val,w.val.2.property,w.property⟩⟩
  invFun w:=⟨⟨w.1,⟨w.2.val,w.2.property.1⟩⟩,w.2.property.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma decorated_coefficient (r:ℕ) (a:Fin r →₀ ℕ) (ha:a.degree=n) :
    (∑κ:Fin n → Fin r,
      if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
        (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
    ∑d:DecoratedLeaf G,(↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) *
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G d.1 i)).coeff a := by
  rw [history_coefficient G r a ha]
  symm
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  change (∑d:LaurentPositive.Decoration (historyWeight G l) (historyWeight_positive G l) G.edgeCount,
    (↑(LaurentRay.vUnit^(2*(d.1.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)*
      (∏i:Fin (historyDimension G+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ)
        (historyProfile G l i)).coeff a)=_
  rw [←Finset.sum_mul,←LaurentPositive.decoration_expansion _ _ _ (historyWeight_support G l)]

lemma required_energy_sum (J:Finset (Fin (n-1))) :
    (∑w:G.RequiredWord J,
      (↑(LaurentRay.vUnit^(2*(G.graphInversions w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=
    ∑w:RequiredDecorated G J,
      (↑(LaurentRay.vUnit^(2*(decoratedEnergy G w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) := by
  have hc:(∑w:G.RequiredWord J,
      (↑(LaurentRay.vUnit^(2*(G.graphInversions w.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=
      ∑κ:G.PacketColor J,
      (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ):=by
    rw [←Equiv.sum_comp (G.requiredColorEquiv J)]
    apply Finset.sum_congr rfl
    intro w hw
    rw [G.requiredColorEquiv_energy]
  rw [hc]
  change (∑κ:{κ:Fin n → Fin (n+1) // G.Proper κ ∧ ∀c,card κ c=card (index J) c},
    (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ.val:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))=_
  rw [sum_subtype_ite (fun κ:Fin n → Fin (n+1)=>G.Proper κ ∧ ∀c,card κ c=card (index J) c)
    (fun κ=>(↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ))]
  have hd:=decorated_coefficient G (n+1) (packetProfile J) (packetProfile_degree J)
  simp only [packetProfile_apply] at hd
  change (∑κ:Fin n → Fin (n+1),if G.Proper κ ∧ (∀i,card κ i=card (index J) i) then
    (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=_ at hd
  apply hd.trans
  rw [←Equiv.sum_comp (requiredDecoratedEquiv G J).symm]
  conv_rhs => rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro d hd
  rw [requiredAnchor_card]
  change (↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)*
    (Fintype.card (RequiredAnchor (historyProfile G d.1) J):LaurentSeries ℚ)=
      ∑y:RequiredAnchor (historyProfile G d.1) J,
        (↑(LaurentRay.vUnit^(2*(leafEnergy G d:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ)
  simp [mul_comm]

end
end TriangularDynamics
end ElementaryPositivity

end

end OAI
