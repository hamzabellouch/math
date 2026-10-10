import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRawAlgebra

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw
open Construction HistoryBulkProducts HistoryBulkSupportConverse HistoryBulkFrequencyTransport
open HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorDiagram HistorySignedSpectatorCRT
open HistoryBulkSpectatorDiagramAverage
variable {q : ℕ} [Fact q.Prime]

theorem evaluate_reference_raw {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (hr : Regular q h)
    (hn : StaticSkeleton V k) (hf : SameFrequencyData h k)
    (hc : Nat.Coprime (bulkProduct k.root.small) q)
    (g : ZMod q→ℂ) (hg : g 0=0) (D : (ZMod q)ˣ) (sign : Bool)
    (Xp Xm : (ZMod q)ˣ) :
    Tree.Parameters.evaluate g D (parameters V outside h hs hr sign) Xp Xm
      (primeArgument q D k.root Xp Xm) (rawLeaves q k)=
      conjugateIf sign (primeSpectator q g D k Xp Xm) := by
  induction h generalizing sign Xp Xm with
  | leaf a => cases k with | leaf b => cases sign <;> rfl
  | node a p u hp hm left right il ir =>
    cases k with
    | node b p' u' hp' hm' left' right' =>
      have hc' := child_bulk_coprime_static hn hc
      simp only [parameters,Tree.Parameters.evaluate,rawLeaves_left,rawLeaves_right,
        frequency_parameters]
      simp only [treePivot_eq_raw hs hr hn hf hc Xp Xm]
      split_ifs with hz
      · rw [primeSpectator,primeSpectator_zero_of_giant q g hg D left' _ _ (Or.inl hz),zero_mul]
        cases sign <;> simp [conjugateIf]
      · rw [outgoing_left_raw hs hr hn hf hc D,outgoing_right_raw hs hr hn hf hc D,
          il left' (History.supported_left hs) (left_regular hr) hn.2.2.1 hf.2.2.2.2.1 hc'.1 sign,
          ir right' (History.supported_right hs) (right_regular hr) hn.2.2.2 hf.2.2.2.2.2 hc'.2 (!sign)]
        exact (conjugateIf_mul_conj sign _ _).symm

theorem bulkDiagram_value_raw {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History l) (hs : h.Supported V outside) (hr : Regular q h)
    (hn : StaticSkeleton V k) (hf : SameFrequencyData h k)
    (hfixed : fixedProduct h.root.small=fixedProduct k.root.small)
    (hc : Nat.Coprime (bulkProduct k.root.small) q)
    (D Xp Xm : (ZMod q)ˣ) (g : ZMod q→ℂ) (hg : g 0=0) :
    (bulkDiagram h hs hr D Xp Xm).value g (rawLeaves q k)=primeSpectator q g D k Xp Xm := by
  cases h with
  | leaf a =>
    cases k with
    | leaf b =>
      simp only [History.root] at hc hfixed
      change g ((leafFrequency a hr D Xp Xm:ZMod q)/
        (Characters.Template.unitConvention (bulkProduct b.small:ZMod q):ZMod q))=
        g (primeArgument q D b Xp Xm)
      rw [Characters.Template.unitConvention_coe _ ((ZMod.isUnit_iff_coprime _ _).mpr hc)]
      congr 1
      simp only [leafFrequency,Units.val_div_eq_div_val,Units.val_mul]
      change (a.frequency:ZMod q)/
        ((D:ZMod q)*(Xp:ZMod q)*(Xm:ZMod q)*(fixedProduct a.small:ZMod q))/
          (bulkProduct b.small:ZMod q)=_
      rw [show a.frequency=b.frequency from hf,hfixed,primeArgument,product_split,Nat.cast_mul]
      simp only [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm]
  | node a p u hp hm left right =>
    cases k with
    | node b p' u' hp' hm' left' right' =>
      simpa only [bulkDiagram,variableDiagram,Tree.Diagram.value,Tree.Parameters.value,parameters,
        Tree.Parameters.evaluate,conjugateIf,Bool.false_eq_true,ite_false] using
        evaluate_reference_raw (.node a p u hp hm left right)
          (.node b p' u' hp' hm' left' right') hs hr hn hf hc g hg D false Xp Xm

end Ostmann.Arithmetic.HistoryBulkSpectatorReferenceRaw

end

end OAI
