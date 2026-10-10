import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramActual
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramProductZero

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedSpectatorCRT HistoryRepresentativeSourceSeparation

theorem residuePairSpectator_eq_mixedDiagramProduct {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) (Xp : ZMod outside.prod) (Xm : (ZMod outside.prod)ˣ) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=
      mixedDiagramProduct h k hs ks hprime hV g Xp Xm := by
  classical
  by_cases hx : IsUnit Xp
  · simp only [mixedDiagramProduct,dite_eq_left hx]
    have he := residuePairSpectator_eq_diagramProduct h k hs ks had hprime hV g hg hx.unit Xm
    simpa only [IsUnit.unit_spec] using he
  · simp only [mixedDiagramProduct,dite_eq_right hx]
    exact residuePairSpectator_zero_of_nonunit_left h k hs ks had hprime g hg Xp Xm hx

theorem actual_residuePairSpectator_eq_mixedDiagramProduct
    (d : Decomposition) {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (Xp : ZMod outside.prod) (Xm : (ZMod outside.prod)ˣ) :
    residuePairSpectator (residueTransform d) outside outside.prod h k (Xp,Xm)=
      mixedDiagramProduct h k hs ks hprime hV (residueTransform d) Xp Xm :=
  residuePairSpectator_eq_mixedDiagramProduct h k hs ks had hprime hV _
    (fun q _=>actual_residueTransform_zero d q) Xp Xm

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
