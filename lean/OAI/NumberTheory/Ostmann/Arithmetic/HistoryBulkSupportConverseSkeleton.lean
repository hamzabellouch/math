import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFrequencyTransport
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextConverse

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryBulkProducts HistorySupportReduction
open HistoryFrequencyResidues HistorySignedDecode HistorySignedNumerators

structure RootStatic (V : ℕ → ℕ) {l : ℕ} (h : History l) : Prop where
  primeSmall : h.root.PrimeSmall
  templateAt : h.root.TemplateAt l
  frequency_ne_zero : h.root.frequency≠0
  frequency_bound : h.root.frequency.natAbs≤V l

structure NodeStatic {l : ℕ} (a : State) (u hp hm : List SmallSlot)
    (left right : History l) : Prop where
  roles : ∀q∈u,q.role=.compensation (l+1)
  split : a.small.Perm (hp++hm)
  leftSmall : left.root.small.Perm (u++hp)
  rightSmall : right.root.small.Perm (u++hm)
  primeComp : ∀q∈u,q.value.Prime
  distinctComp : (u.map SmallSlot.value).Nodup

def StaticSkeleton (V : ℕ → ℕ) : {l : ℕ} → History l → Prop
  | _,h@(.leaf _) => RootStatic V h
  | _,h@(.node a _ u hp hm left right) =>
    RootStatic V h ∧ NodeStatic a u hp hm left right ∧
      StaticSkeleton V left ∧ StaticSkeleton V right

theorem StaticSkeleton.root {l : ℕ} {V : ℕ → ℕ} {h : History l}
    (hs : StaticSkeleton V h) : RootStatic V h := by
  cases h with
  | leaf a => exact hs
  | node a p u hp hm left right => exact hs.1

theorem rootStatic_of_supported {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) : RootStatic V h :=
  ⟨(rootData_of_supported hs).2.1,History.supported_template hs,
    History.supported_root_frequency_ne_zero hs,History.supported_root_frequency_bound hs⟩

theorem staticSkeleton_of_supported {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) (hlarge : LargePrimes V h) :
    StaticSkeleton V h := by
  induction h with
  | leaf a => exact rootStatic_of_supported hs
  | node a p u hp hm left right il ir =>
    have ht := localTests_of_supported_node hs hlarge.2.1
    exact ⟨rootStatic_of_supported hs,⟨History.supported_compensation_roles hs,History.supported_small_split hs,
      (History.supported_child_small hs).1,(History.supported_child_small hs).2,ht.2.1,ht.1⟩,
      il (History.supported_left hs) hlarge.2.2.1,
      ir (History.supported_right hs) hlarge.2.2.2⟩

theorem NodeStatic.bulk_products {l : ℕ} {a : State} {u hp hm : List SmallSlot}
    {left right : History l} (hs : NodeStatic a u hp hm left right) :
    bulkProduct a.small=bulkProduct hp*bulkProduct hm ∧
      bulkProduct left.root.small=bulkProduct hp ∧ bulkProduct right.root.small=bulkProduct hm := by
  have hu := compensation_bulkProduct (l+1) u hs.roles
  refine ⟨(bulkProduct_perm hs.split).trans (bulkProduct_append hp hm),?_,?_⟩
  · rw [bulkProduct_perm hs.leftSmall,bulkProduct_append,hu,one_mul]
  · rw [bulkProduct_perm hs.rightSmall,bulkProduct_append,hu,one_mul]

theorem frequencyLeaves_product_coe_static {l : ℕ} {V : ℕ → ℕ} (h : History l)
    (hs : StaticSkeleton V h) (R n : ℕ) (hR : Nat.Coprime (bulkProduct h.root.small) R) :
    (Characters.BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) h):ZMod (R^n))=
      (bulkProduct h.root.small:ZMod (R^n)) := by
  induction h with
  | leaf a =>
    exact Characters.Template.unitConvention_coe _ ((ZMod.isUnit_iff_coprime _ _).mpr (hR.pow_right n))
  | node a p u hp hm left right il ir =>
    have hb := hs.2.1.bulk_products
    have hc : Nat.Coprime (bulkProduct hp) R ∧ Nat.Coprime (bulkProduct hm) R := by
      rw [History.root,hb.1] at hR
      exact Nat.coprime_mul_iff_left.mp hR
    change (↑(Characters.BinaryHaar.product (frequencyLeaves (R^n) left) *
      Characters.BinaryHaar.product (frequencyLeaves (R^n) right)):ZMod (R^n))=_
    rw [Units.val_mul,il hs.2.2.1 (by simpa only [hb.2.1] using hc.1),
      ir hs.2.2.2 (by simpa only [hb.2.2] using hc.2),hb.2.1,hb.2.2,History.root,hb.1,Nat.cast_mul]

theorem frequencyLeaves_child_products_static {l : ℕ} {V : ℕ → ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : StaticSkeleton V (.node a p u hp hm left right))
    (R n : ℕ) (hR : Nat.Coprime (bulkProduct a.small) R) :
    (Characters.BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) left):ZMod (R^n))=
      (bulkProduct hp:ZMod (R^n)) ∧
    (Characters.BinaryHaar.product (G:=(ZMod (R^n))ˣ) (frequencyLeaves (R^n) right):ZMod (R^n))=
      (bulkProduct hm:ZMod (R^n)) := by
  have hb := hs.2.1.bulk_products
  rw [hb.1] at hR
  have hc := Nat.coprime_mul_iff_left.mp hR
  constructor
  · rw [←hb.2.1]
    exact frequencyLeaves_product_coe_static left hs.2.2.1 R n (by simpa only [hb.2.1] using hc.1)
  · rw [←hb.2.2]
    exact frequencyLeaves_product_coe_static right hs.2.2.2 R n (by simpa only [hb.2.2] using hc.2)

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
