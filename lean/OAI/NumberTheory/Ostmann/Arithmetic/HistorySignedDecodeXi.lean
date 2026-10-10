import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeTreeExpression
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeZero
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightPositiveSupportActual

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedDecode
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicEncoding
open HistoryOccurrenceVariables

def signedGiantSample {l : ℕ} (h : History l) (Xp Xm : ℤ) : Key h → ℝ
  | .inl false => Xp
  | .inl true => Xm
  | .inr (.inl i) => (h.root.small.get i).value
  | .inr (.inr i) => (internalSlot h i).value

theorem symbolicHistory_rebuild_giantsAgree {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    TreeGiantsAgree (signedGiantSample h Xp Xm) h (symbolicHistory h hs) (rebuild h Xp Xm) := by
  apply encode_rebuild_giantsAgree h hs (rootExpr h) (compensationExpr h)
    (signedGiantSample h Xp Xm) Xp Xm rfl rfl _ _ hi
  · intro i
    rfl
  · intro i
    rfl

theorem symbolicHistory_allPivotsPositive_iff_rebuild
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) :
    AllPivotsPositive (signedGiantSample h Xp Xm) h (symbolicHistory h hs) ↔
      (rebuild h Xp Xm).PivotsPositive :=
  TreeGiantsAgree.allPivotsPositive_iff h _ Xp Xm
    (symbolicHistory_rebuild_giantsAgree h hs Xp Xm hi)

theorem actualScalar_ne_zero_rebuild_pivotsPositive
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard)
    (hz : actualRealHistoryScalar b s X tb td G outside h hs (signedGiantSample h Xp Xm)≠0) :
    (rebuild h Xp Xm).PivotsPositive := by
  apply (symbolicHistory_allPivotsPositive_iff_rebuild h hs Xp Xm hi).mp
  exact allPivotsPositive_of_actualRealHistoryScalar_ne_zero b s X tb td G outside h hs _ hz

theorem actualXi_ne_zero_rebuild_positiveIntegral
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h h' : History l)
    (hs : h.Supported V outside) (hs' : h'.Supported V outside) (Xp Xm : ℤ)
    (hp : 0<Xp) (hm : 0<Xm)
    (hi : (rebuild h Xp Xm).IntegralGuard) (hi' : (rebuild h' Xp Xm).IntegralGuard)
    (hz : actualRealXi b s X tb td G outside h h' hs hs'
      (signedGiantSample h Xp Xm) (signedGiantSample h' Xp Xm)≠0) :
    (rebuild h Xp Xm).PositiveIntegral ∧ (rebuild h' Xp Xm).PositiveIntegral := by
  have hh : actualRealHistoryScalar b s X tb td G outside h hs (signedGiantSample h Xp Xm)≠0 ∧
      actualRealHistoryScalar b s X tb td G outside h' hs' (signedGiantSample h' Xp Xm)≠0 := by
    simpa only [actualRealXi,mul_ne_zero_iff,star_ne_zero] using hz
  exact ⟨rebuild_positiveIntegral h Xp Xm hp hm hi
      (actualScalar_ne_zero_rebuild_pivotsPositive b s X tb td G outside h hs Xp Xm hi hh.1),
    rebuild_positiveIntegral h' Xp Xm hp hm hi'
      (actualScalar_ne_zero_rebuild_pivotsPositive b s X tb td G outside h' hs' Xp Xm hi' hh.2)⟩

theorem actualXi_eq_zero_of_not_rebuild_pivotsPositive
    (b s : ℕ) (X tb td G : ℝ) (outside : List ℕ)
    {l : ℕ} {V : ℕ → ℕ} (h h' : History l)
    (hs : h.Supported V outside) (hs' : h'.Supported V outside) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (hi' : (rebuild h' Xp Xm).IntegralGuard)
    (hn : ¬(rebuild h Xp Xm).PivotsPositive ∨ ¬(rebuild h' Xp Xm).PivotsPositive) :
    actualRealXi b s X tb td G outside h h' hs hs'
      (signedGiantSample h Xp Xm) (signedGiantSample h' Xp Xm)=0 := by
  apply actualRealXi_eq_zero_of_not_allPivotsPositive b s X tb td G outside h h' hs hs'
  exact hn.imp
    (fun hh hx => hh ((symbolicHistory_allPivotsPositive_iff_rebuild h hs Xp Xm hi).mp hx))
    (fun hh hx => hh ((symbolicHistory_allPivotsPositive_iff_rebuild h' hs' Xp Xm hi').mp hx))

end Ostmann.Arithmetic.HistorySignedDecode

end

end OAI
