import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverageBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage
open Construction HistoryResidueRegular HistoryTreeParameters HistoryBulkProducts
open HistorySignedSpectatorDiagram HistoryBulkDiagramParameters
variable {q : ℕ} [Fact q.Prime]

def leafFrequency (a : State) (hr : Regular q (.leaf a)) (D Xp Xm : (ZMod q)ˣ) : (ZMod q)ˣ :=
  frequencyUnit (.leaf a) hr/(D*Xp*Xm*fixedUnit (.leaf a) hr)

def bulkDiagram {V : ℕ→ℕ} {outside : List ℕ} :
    {l : ℕ}→(h : History l)→h.Supported V outside→Regular q h→
      (ZMod q)ˣ→(ZMod q)ˣ→(ZMod q)ˣ→Tree.Diagram (ZMod q) l
  | _,.leaf a,_,hr,D,Xp,Xm =>
    ⟨.leaf (leafFrequency a hr D Xp Xm) false,D,Xp,Xm,True.intro,True.intro⟩
  | _,.node a p u hp hm left right,hs,hr,D,Xp,Xm =>
    variableDiagram (.node a p u hp hm left right) hs hr D Xp Xm

theorem leafDiagram_value {V : ℕ→ℕ} {outside : List ℕ} (a : State)
    (hs : (History.leaf a).Supported V outside) (hr : Regular q (.leaf a))
    (D Xp Xm : (ZMod q)ˣ) (g : ZMod q→ℂ) :
    (bulkDiagram (.leaf a) hs hr D Xp Xm).value g (leafBulk (.leaf a) hr)=
      primeSpectator q g D (.leaf a) Xp Xm := by
  change g ((leafFrequency a hr D Xp Xm:ZMod q)/(bulkUnit (.leaf a) hr:ZMod q))=
    g (primeArgument q D a Xp Xm)
  congr 1
  simp only [leafFrequency,Units.val_div_eq_div_val,Units.val_mul]
  change (a.frequency:ZMod q)/
    ((D:ZMod q)*(Xp:ZMod q)*(Xm:ZMod q)*(fixedProduct a.small:ZMod q))/
      (bulkProduct a.small:ZMod q)=_
  rw [primeArgument,product_split,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm]

theorem bulkDiagram_value {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (hr : Regular q h)
    (D Xp Xm : (ZMod q)ˣ) (g : ZMod q→ℂ) (hg : g 0=0) :
    (bulkDiagram h hs hr D Xp Xm).value g (leafBulk h hr)=primeSpectator q g D h Xp Xm := by
  cases h with
  | leaf a => exact leafDiagram_value a hs hr D Xp Xm g
  | node a p u hp hm left right => exact variableDiagram_value _ hs hr g hg D Xp Xm

theorem leafFrequency_eq (a b : State) (hra : Regular q (.leaf a)) (hrb : Regular q (.leaf b))
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue) (D Xp Xm : (ZMod q)ˣ) :
    leafFrequency a hra D Xp Xm=leafFrequency b hrb D Xp Xm := by
  apply Units.ext
  simp only [leafFrequency,Units.val_div_eq_div_val,Units.val_mul]
  change (a.frequency:ZMod q)/((D:ZMod q)*(Xp:ZMod q)*(Xm:ZMod q)*(fixedProduct a.small:ZMod q))=
    (b.frequency:ZMod q)/((D:ZMod q)*(Xp:ZMod q)*(Xm:ZMod q)*(fixedProduct b.small:ZMod q))
  rw [hf,fixedProduct_eq_of_erase_eq hab]

theorem bulkDiagram_decode_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l)
    (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (ha : (decodeHistory sources seed V l a c).Supported V outside)
    (hb : (decodeHistory sources seed V l b c).Supported V outside)
    (hra : Regular q (decodeHistory sources seed V l a c))
    (hrb : Regular q (decodeHistory sources seed V l b c)) (D Xp Xm : (ZMod q)ˣ) :
    bulkDiagram (decodeHistory sources seed V l a c) ha hra D Xp Xm=
      bulkDiagram (decodeHistory sources seed V l b c) hb hrb D Xp Xm := by
  cases l with
  | zero =>
    have he := leafFrequency_eq a b hra hrb hf hab D Xp Xm
    simp only [decodeHistory,bulkDiagram]
    rw [he]
  | succ l => exact variableDiagram_decode_eq sources seed V outside l a b c hf hab ha hb hra hrb D Xp Xm

theorem primeSpectator_decode_eq_referenceBulkDiagram (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b : State)
    (c : HistoryChoices sources seed V l) (hf : a.frequency=b.frequency)
    (hab : a.small.map eraseBulkValue=b.small.map eraseBulkValue)
    (ha : (decodeHistory sources seed V l a c).Supported V outside)
    (hb : (decodeHistory sources seed V l b c).Supported V outside)
    (hq : q∈outside) (hV : ∀j≤l,V j<q)
    (g : ZMod q→ℂ) (hg : g 0=0) (D Xp Xm : (ZMod q)ˣ) :
    primeSpectator q g D (decodeHistory sources seed V l b c) Xp Xm=
      (bulkDiagram (decodeHistory sources seed V l a c) ha
        (supported_regular _ ha hq hV) D Xp Xm).value g
        (leafBulk (decodeHistory sources seed V l b c) (supported_regular _ hb hq hV)) := by
  rw [bulkDiagram_decode_eq sources seed V outside l a b c hf hab ha hb
    (supported_regular _ ha hq hV) (supported_regular _ hb hq hV) D Xp Xm]
  exact (bulkDiagram_value _ hb (supported_regular _ hb hq hV) D Xp Xm g hg).symm

end Ostmann.Arithmetic.HistoryBulkSpectatorDiagramAverage

end

end OAI
