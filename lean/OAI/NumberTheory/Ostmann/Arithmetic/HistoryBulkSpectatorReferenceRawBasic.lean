import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverageLeaf
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSkeleton
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairedFrequencyAverageHaarBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction Characters HistoryBulkProducts HistoryBulkSupportConverse
open HistoryFrequencyResidues HistoryPairedFrequencyAverageHaar
open HistoryBulkFrequencyTransport HistoryResidueRegular HistoryTreeParameters
open HistorySignedSpectatorDiagram HistorySignedSpectatorCRT
variable {q : ℕ} [Fact q.Prime]

def rawLeaves {l : ℕ} (q : ℕ) (h : History l) : Tree.Leaves l → (ZMod q)ˣ :=
  leafValue (frequencyLeaves q h)

@[simp] theorem rawLeaves_left {l : ℕ} (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (left right : History l) :
    Tree.Parameters.childLeaves (rawLeaves q (.node a p u hp hm left right)) false = rawLeaves q left := by
  funext path
  simp [rawLeaves,Tree.Parameters.childLeaves,frequencyLeaves,leafValue]

@[simp] theorem rawLeaves_right {l : ℕ} (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (left right : History l) :
    Tree.Parameters.childLeaves (rawLeaves q (.node a p u hp hm left right)) true = rawLeaves q right := by
  funext path
  simp [rawLeaves,Tree.Parameters.childLeaves,frequencyLeaves,leafValue]

omit [Fact q.Prime] in
theorem child_bulk_coprime_static [_primeFact : Fact q.Prime] {l : ℕ} {V : ℕ→ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : StaticSkeleton V (.node a p u hp hm left right))
    (hc : Nat.Coprime (bulkProduct a.small) q) :
    Nat.Coprime (bulkProduct left.root.small) q ∧ Nat.Coprime (bulkProduct right.root.small) q := by
  have hb := hs.2.1.bulk_products
  rw [hb.1] at hc
  simpa only [hb.2.1,hb.2.2] using Nat.coprime_mul_iff_left.mp hc

theorem leafProduct_rawLeaves {l : ℕ} {V : ℕ→ℕ} (h : History l)
    (hs : StaticSkeleton V h) (hc : Nat.Coprime (bulkProduct h.root.small) q) :
    (Tree.Parameters.leafProduct (rawLeaves q h):ZMod q)=(bulkProduct h.root.small:ZMod q) := by
  induction h with
  | leaf a =>
    simpa [Tree.Parameters.leafProduct,Tree.Leaves,rawLeaves,frequencyLeaves,leafValue,History.root] using
      (Template.unitConvention_coe (bulkProduct a.small:ZMod q)
        ((ZMod.isUnit_iff_coprime _ _).mpr hc))
  | node a p u hp hm left right il ir =>
    have hc' := child_bulk_coprime_static hs hc
    rw [Tree.Density.leafProduct_split]
    change (↑(Tree.Parameters.leafProduct (rawLeaves q left) *
      Tree.Parameters.leafProduct (rawLeaves q right)):ZMod q)=_
    rw [Units.val_mul,il hs.2.2.1 hc'.1,ir hs.2.2.2 hc'.2]
    rw [hs.2.1.bulk_products.2.1,hs.2.1.bulk_products.2.2]
    change (bulkProduct hp:ZMod q)*(bulkProduct hm:ZMod q)=(bulkProduct a.small:ZMod q)
    rw [hs.2.1.bulk_products.1,Nat.cast_mul]

variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
variable {a b : State} {p p' : ℕ} {u hp hm u' hp' hm' : List SmallSlot}
variable {left right left' right' : History l}

theorem left_product_raw
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (.node a p u hp hm left right))
    (hn : StaticSkeleton V (.node b p' u' hp' hm' left' right'))
    (hf : SameFrequencyData (.node a p u hp hm left right) (.node b p' u' hp' hm' left' right'))
    (hc : Nat.Coprime (bulkProduct b.small) q) (X : (ZMod q)ˣ) :
    ((X*leftConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q left'):(ZMod q)ˣ):ZMod q)=
      (X:ZMod q)*((hp'.map SmallSlot.value).prod:ZMod q) := by
  rw [Units.val_mul,leafProduct_rawLeaves left' hn.2.2.1 (child_bulk_coprime_static hn hc).1]
  change (X:ZMod q)*(fixedProduct hp:ZMod q)*(bulkProduct left'.root.small:ZMod q)=_
  rw [hf.2.1,hn.2.1.bulk_products.2.1,product_split hp',Nat.cast_mul,mul_assoc]

theorem right_product_raw
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hr : Regular q (.node a p u hp hm left right))
    (hn : StaticSkeleton V (.node b p' u' hp' hm' left' right'))
    (hf : SameFrequencyData (.node a p u hp hm left right) (.node b p' u' hp' hm' left' right'))
    (hc : Nat.Coprime (bulkProduct b.small) q) (X : (ZMod q)ˣ) :
    ((X*rightConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q right'):(ZMod q)ˣ):ZMod q)=
      (X:ZMod q)*((hm'.map SmallSlot.value).prod:ZMod q) := by
  rw [Units.val_mul,leafProduct_rawLeaves right' hn.2.2.2 (child_bulk_coprime_static hn hc).2]
  change (X:ZMod q)*(fixedProduct hm:ZMod q)*(bulkProduct right'.root.small:ZMod q)=_
  rw [hf.2.2.1,hn.2.1.bulk_products.2.2,product_split hm',Nat.cast_mul,mul_assoc]

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
