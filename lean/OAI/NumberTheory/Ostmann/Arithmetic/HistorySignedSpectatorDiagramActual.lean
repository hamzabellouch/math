import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramUnitProduct
import OAI.NumberTheory.Ostmann.Construction.ActualTests

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedSpectatorCRT HistoryRepresentativeSourceSeparation

def diagramProduct {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hprime : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (Xp Xm : (ZMod outside.prod)ˣ) : ℂ :=
  (outside.attach.map (fun q=>
    variableDiagramFactor h hs q.val q.property (hprime q.val q.property)
      (hV q.val q.property) (g q.val)
      (ZMod.unitsMap (List.dvd_prod q.property) Xp) (ZMod.unitsMap (List.dvd_prod q.property) Xm)*
    conj (variableDiagramFactor k ks q.val q.property (hprime q.val q.property)
      (hV q.val q.property) (g q.val)
      (ZMod.unitsMap (List.dvd_prod q.property) Xp) (ZMod.unitsMap (List.dvd_prod q.property) Xm)))).prod

def mixedDiagramProduct {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hprime : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (Xp : ZMod outside.prod) (Xm : (ZMod outside.prod)ˣ) : ℂ := by
  classical
  exact if hx : IsUnit Xp then diagramProduct h k hs ks hprime hV g hx.unit Xm else 0

theorem actual_residueTransform_zero (d : Decomposition) (q : ℕ) :
    residueTransform d q 0=0 := by
  by_cases hq : q=0
  · simp only [residueTransform,hq,dite_true]
  · let : NeZero q := ⟨hq⟩
    simp only [residueTransform_eq,Supply.additiveTransform_zero]

theorem residuePairSpectator_eq_diagramProduct {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) (Xp Xm : (ZMod outside.prod)ˣ) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=
      diagramProduct h k hs ks hprime hV g Xp Xm :=
  residuePairSpectator_eq_variableDiagrams h k hs ks had hprime hV g hg Xp Xm

theorem actual_residuePairSpectator_eq_diagramProduct
    (d : Decomposition) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (Xp Xm : (ZMod outside.prod)ˣ) :
    residuePairSpectator (residueTransform d) outside outside.prod h k (Xp,Xm)=
      diagramProduct h k hs ks hprime hV (residueTransform d) Xp Xm :=
  residuePairSpectator_eq_diagramProduct h k hs ks had hprime hV _
    (fun q _=>actual_residueTransform_zero d q) Xp Xm

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
