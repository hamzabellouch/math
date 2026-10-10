import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction HistoryBulkProducts HistoryBulkSupportConverse HistoryBulkFrequencyTransport
open HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorDiagram HistorySignedSpectatorCRT
variable {q : ℕ} [Fact q.Prime]
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
variable {a b : State} {p p' : ℕ} {u hp hm u' hp' hm' : List SmallSlot}
variable {left right left' right' : History l}
variable (hs : (History.node a p u hp hm left right).Supported V outside)
variable (hr : Regular q (.node a p u hp hm left right))
variable (hn : StaticSkeleton V (.node b p' u' hp' hm' left' right'))
variable (hf : SameFrequencyData (.node a p u hp hm left right) (.node b p' u' hp' hm' left' right'))
variable (hc : Nat.Coprime (bulkProduct b.small) q)

include hn hf hc

theorem treePivot_eq_raw (Xp Xm : (ZMod q)ˣ) :
    ((frequencyUnit left (left_regular hr):ZMod q)*
      ((Xm*rightConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q right'):(ZMod q)ˣ):ZMod q)-
      (frequencyUnit right (right_regular hr):ZMod q)*
      ((Xp*leftConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q left'):(ZMod q)ˣ):ZMod q))/
      ((frequencyUnit _ hr:ZMod q)*(splitConstant hs hr:ZMod q))=
      residuePivot q b left'.root.frequency right'.root.frequency u' hp' hm' Xp Xm := by
  rw [left_product_raw hs hr hn hf hc Xp,right_product_raw hs hr hn hf hc Xm]
  change ((left.root.frequency:ZMod q)*((Xm:ZMod q)*((hm'.map SmallSlot.value).prod:ZMod q))-
    (right.root.frequency:ZMod q)*((Xp:ZMod q)*((hp'.map SmallSlot.value).prod:ZMod q)))/
    ((a.frequency:ZMod q)*((u.map SmallSlot.value).prod:ZMod q))=_
  rw [hf.1,hf.2.2.2.1,hf.2.2.2.2.1.root_frequency_eq,hf.2.2.2.2.2.root_frequency_eq]
  rfl

theorem outgoing_left_raw (D P X : (ZMod q)ˣ) :
    (frequencyUnit left (left_regular hr):ZMod q)/
      ((D:ZMod q)*(P:ZMod q)*(splitConstant hs hr:ZMod q)*
        ((X*leftConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q left'):(ZMod q)ˣ):ZMod q))=
      primeArgument q D left'.root P X := by
  rw [left_product_raw hs hr hn hf hc X]
  change (left.root.frequency:ZMod q)/
    ((D:ZMod q)*(P:ZMod q)*((u.map SmallSlot.value).prod:ZMod q)*
      ((X:ZMod q)*((hp'.map SmallSlot.value).prod:ZMod q)))=_
  have hsmall : (left'.root.small.map SmallSlot.value).prod=
      (u'.map SmallSlot.value).prod*(hp'.map SmallSlot.value).prod := by
    simpa only [List.map_append,List.prod_append] using (hn.2.1.leftSmall.map SmallSlot.value).prod_eq
  rw [hf.2.2.2.1,hf.2.2.2.2.1.root_frequency_eq]
  simp only [primeArgument,hsmall,Nat.cast_mul,div_eq_mul_inv,mul_assoc,mul_left_comm]

theorem outgoing_right_raw (D P X : (ZMod q)ˣ) :
    (frequencyUnit right (right_regular hr):ZMod q)/
      ((D:ZMod q)*(P:ZMod q)*(splitConstant hs hr:ZMod q)*
        ((X*rightConstant hs hr*Tree.Parameters.leafProduct (rawLeaves q right'):(ZMod q)ˣ):ZMod q))=
      primeArgument q D right'.root P X := by
  rw [right_product_raw hs hr hn hf hc X]
  change (right.root.frequency:ZMod q)/
    ((D:ZMod q)*(P:ZMod q)*((u.map SmallSlot.value).prod:ZMod q)*
      ((X:ZMod q)*((hm'.map SmallSlot.value).prod:ZMod q)))=_
  have hsmall : (right'.root.small.map SmallSlot.value).prod=
      (u'.map SmallSlot.value).prod*(hm'.map SmallSlot.value).prod := by
    simpa only [List.map_append,List.prod_append] using (hn.2.1.rightSmall.map SmallSlot.value).prod_eq
  rw [hf.2.2.2.1,hf.2.2.2.2.2.root_frequency_eq]
  simp only [primeArgument,hsmall,Nat.cast_mul,div_eq_mul_inv,mul_assoc,mul_left_comm]

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
