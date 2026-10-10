import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramEvaluation
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramProduct

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistoryResidueRegular HistoryTreeParameters HistorySignedSpectatorCRT
open HistoryRepresentativeSourceSeparation

def variableDiagramFactor {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (q : ℕ)
    (hq : q∈outside) (hprime : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : ZMod q→ℂ) (Xp Xm : (ZMod q)ˣ) : ℂ := by
  letI : Fact q.Prime := ⟨hprime⟩
  exact (variableDiagram h hs (supported_regular h hs hq hV)
    (denominatorUnit hs hq) Xp Xm).value g (leafBulk h (supported_regular h hs hq hV))

theorem variableDiagramFactor_eq {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h : History (l+1)) (hs : h.Supported V outside) (q : ℕ)
    (hq : q∈outside) (hprime : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : ZMod q→ℂ) (hg : g 0=0) (Xp Xm : (ZMod q)ˣ) :
    variableDiagramFactor h hs q hq hprime hV g Xp Xm=
      primeSpectator q g ((outsideProduct outside/q:ℕ):ZMod q) h Xp Xm := by
  let : Fact q.Prime := ⟨hprime⟩
  unfold variableDiagramFactor
  rw [variableDiagram_value _ _ _ g hg,denominatorUnit_coe]

theorem residuePairSpectator_eq_variableDiagrams {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l+1,V j<q) (g : (q:ℕ)→ZMod q→ℂ)
    (hg : ∀q∈outside,g q 0=0) (Xp Xm : (ZMod outside.prod)ˣ) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=
      (outside.attach.map (fun q =>
        variableDiagramFactor h hs q.val q.property (hprime q.val q.property)
          (hV q.val q.property) (g q.val)
          (ZMod.unitsMap (List.dvd_prod q.property) Xp) (ZMod.unitsMap (List.dvd_prod q.property) Xm)*
        conj (variableDiagramFactor k ks q.val q.property (hprime q.val q.property)
          (hV q.val q.property) (g q.val)
          (ZMod.unitsMap (List.dvd_prod q.property) Xp) (ZMod.unitsMap (List.dvd_prod q.property) Xm)))).prod := by
  rw [residuePairSpectator_eq_primeProduct_actual h k hs ks had]
  have he (f : ℕ→ℂ) : outside.attach.map (fun q=>f q.val)=outside.map f := by
    calc
      _ = (outside.attach.map Subtype.val).map f := (List.map_map ..).symm
      _ = _ := by rw [List.attach_map_subtype_val]
  rw [←he]
  apply congrArg List.prod
  apply List.map_congr_left
  intro q _
  rw [variableDiagramFactor_eq h hs q.val q.property (hprime q.val q.property)
    (hV q.val q.property) (g q.val) (hg q.val q.property),
    variableDiagramFactor_eq k ks q.val q.property (hprime q.val q.property)
      (hV q.val q.property) (g q.val) (hg q.val q.property)]
  rfl

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
