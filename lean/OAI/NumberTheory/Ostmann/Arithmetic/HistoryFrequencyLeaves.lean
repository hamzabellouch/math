import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyExposure

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction HistoryBulkProducts Characters
open Characters.Template (unitConvention unitConvention_coe)

def frequencyLeaves (Q : ℕ) : {l : ℕ} → History l → BinaryHaar.Leaves (ZMod Q)ˣ l
  | 0,.leaf a => unitConvention (bulkProduct a.small:ZMod Q)
  | _+1,.node _ _ _ _ _ left right => (frequencyLeaves Q left,frequencyLeaves Q right)

theorem child_bulk_coprime {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (R : ℕ) (hR : Nat.Coprime (bulkProduct a.small) R) :
    Nat.Coprime (bulkProduct left.root.small) R ∧
      Nat.Coprime (bulkProduct right.root.small) R := by
  rw [(supported_product_split hs).1] at hR
  have h := Nat.coprime_mul_iff_left.mp hR
  have hc := supported_child_products hs (History.supported_compensation_roles hs)
  simpa only [hc.1,hc.2.1] using h

theorem frequencyLeaves_product_coe {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside)
    (R n : ℕ) (hR : Nat.Coprime (bulkProduct h.root.small) R) :
    (BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) h):ZMod (R^n))=
      (bulkProduct h.root.small:ZMod (R^n)) := by
  induction h with
  | leaf a =>
      exact unitConvention_coe _ ((ZMod.isUnit_iff_coprime _ _).mpr (hR.pow_right n))
  | @node l a p comp hp hm left right ihl ihr =>
      have hc := child_bulk_coprime hs R hR
      change (↑(BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) left) *
        BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) right)):ZMod (R^n))=_
      rw [Units.val_mul,ihl (History.supported_left hs) hc.1,
        ihr (History.supported_right hs) hc.2]
      have hh := supported_child_products hs (History.supported_compensation_roles hs)
      change (bulkProduct left.root.small:ZMod (R^n))*(bulkProduct right.root.small:ZMod (R^n))=
        (bulkProduct a.small:ZMod (R^n))
      rw [hh.1,hh.2.1,(supported_product_split hs).1,Nat.cast_mul]

theorem frequencyLeaves_child_products {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {comp hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p comp hp hm left right).Supported V outside)
    (R n : ℕ) (hR : Nat.Coprime (bulkProduct a.small) R) :
    (BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) left):ZMod (R^n))=(bulkProduct hp:ZMod (R^n)) ∧
    (BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) right):ZMod (R^n))=(bulkProduct hm:ZMod (R^n)) := by
  have hc := child_bulk_coprime hs R hR
  have hh := supported_child_products hs (History.supported_compensation_roles hs)
  constructor
  · simpa only [hh.1] using frequencyLeaves_product_coe left (History.supported_left hs) R n hc.1
  · simpa only [hh.2.1] using frequencyLeaves_product_coe right (History.supported_right hs) R n hc.2

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
