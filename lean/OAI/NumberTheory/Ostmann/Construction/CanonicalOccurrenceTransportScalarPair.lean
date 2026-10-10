import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSmoothXi
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportPairMaps
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalar

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistorySymbolicEncoding Arithmetic.HistoryOccurrenceVariables
open Arithmetic.HistoryPairPattern Arithmetic.HistoryPairSmoothXi

theorem pairedRealXi_eq_of_plans (seed : List SourceSlot)
    {l : ℕ} {V W : ℕ → ℕ} {outside : List ℕ}
    (h k h' k' : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hs' : h'.Supported W outside) (ks' : k'.Supported W outside)
    (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
    (hh' : TreeSourceLabels seed h') (hk' : TreeSourceLabels seed k')
    (hp : SamePairPattern seed h k h' k' hh hk hh' hk')
    (hplan : plan h hs=plan h' hs') (kplan : plan k ks=plan k' ks')
    (b s : ℕ) (X tb td G : ℝ) (x : PairKey h' k' → ℝ) :
    pairedRealXi b s X tb td G h k hs ks
      (x ∘ pairKeyEquiv seed h k h' k' hh hk hh' hk' hp)=
    pairedRealXi b s X tb td G h' k' hs' ks' x := by
  unfold pairedRealXi actualRealXi
  apply congrArg₂ (fun a b : ℂ => a*star b)
  · apply actualRealHistoryScalar_eq_of_coordinates seed h h' hs hs' hh hh' hplan
    intro i
    simp only [Function.comp_apply,pairKeyEquiv_left]
  · apply actualRealHistoryScalar_eq_of_coordinates seed k k' ks ks' hk hk' kplan
    intro i
    simp only [Function.comp_apply,pairKeyEquiv_right]

theorem decoded_pairedRealXi_eq (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a b a' b' : State)
    (c d c' d' : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hb' : Template.Matches (Template.current seed l) b'.small)
    (haa' : a.frequency=a'.frequency) (hbb' : b.frequency=b'.frequency)
    (hcc' : historyFrequencies sources seed V l c=historyFrequencies sources seed V l c')
    (hdd' : historyFrequencies sources seed V l d=historyFrequencies sources seed V l d')
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hd : (decodeHistory sources seed V l b d).Supported V outside)
    (hc' : (decodeHistory sources seed V l a' c').Supported V outside)
    (hd' : (decodeHistory sources seed V l b' d').Supported V outside)
    (hp : SamePairPattern seed
      (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b d)
      (decodeHistory sources seed V l a' c') (decodeHistory sources seed V l b' d')
      (decoded_tree_source_labels sources seed V l a c ha)
      (decoded_tree_source_labels sources seed V l b d hb)
      (decoded_tree_source_labels sources seed V l a' c' ha')
      (decoded_tree_source_labels sources seed V l b' d' hb'))
    (bcount scount : ℕ) (X tb td G : ℝ)
    (x : PairKey (decodeHistory sources seed V l a' c') (decodeHistory sources seed V l b' d') → ℝ) :
    pairedRealXi bcount scount X tb td G
      (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b d) hc hd
      (x ∘ pairKeyEquiv seed _ _ _ _
        (decoded_tree_source_labels sources seed V l a c ha)
        (decoded_tree_source_labels sources seed V l b d hb)
        (decoded_tree_source_labels sources seed V l a' c' ha')
        (decoded_tree_source_labels sources seed V l b' d' hb') hp)=
    pairedRealXi bcount scount X tb td G
      (decodeHistory sources seed V l a' c') (decodeHistory sources seed V l b' d') hc' hd' x :=
  pairedRealXi_eq_of_plans seed _ _ _ _ hc hd hc' hd' _ _ _ _ hp
    (decoded_plan_eq sources seed V outside l a a' c c' ha ha' haa' hcc' hc hc')
    (decoded_plan_eq sources seed V outside l b b' d d' hb hb' hbb' hdd' hd hd')
    bcount scount X tb td G x

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
