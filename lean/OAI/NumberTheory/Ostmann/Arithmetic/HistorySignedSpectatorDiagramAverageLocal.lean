import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverageBasic

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage
open Construction HistorySignedSpectatorCRT HistorySignedSpectatorDiagram
open HistoryCRTIntegration HistoryRepresentativeSourceSeparation ResidueHaar

def localDiagramPair {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (q : ℕ) (hq : q∈outside) (hp : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (z : UnitPair q) : ℂ :=
  variableDiagramFactor h hs q hq hp hV (g q) z.1 z.2 *
    conj (variableDiagramFactor k ks q hq hp hV (g q) z.1 z.2)

def localMixedDiagramPair {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (q : ℕ) (hq : q∈outside) (hp : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (z : MixedPair q) : ℂ := by
  classical
  exact if hx : IsUnit z.1 then localDiagramPair h k hs ks q hq hp hV g (hx.unit,z.2) else 0

theorem primePair_eq_localDiagramPair {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (q : ℕ) (hq : q∈outside) (hp : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (hg : g q 0=0) (z : UnitPair q) :
    primePair h k g outside q (z.1,z.2)=localDiagramPair h k hs ks q hq hp hV g z := by
  rw [localDiagramPair,variableDiagramFactor_eq h hs q hq hp hV (g q) hg,
    variableDiagramFactor_eq k ks q hq hp hV (g q) hg]
  rfl

theorem primePair_eq_localMixedDiagramPair {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}
    (h k : History (l+1)) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (q : ℕ) (hq : q∈outside) (hp : q.Prime) (hV : ∀j≤l+1,V j<q)
    (g : (q:ℕ)→ZMod q→ℂ) (hg : g q 0=0) (z : MixedPair q) :
    primePair h k g outside q (z.1,z.2)=localMixedDiagramPair h k hs ks q hq hp hV g z := by
  classical
  let : Fact q.Prime := ⟨hp⟩
  by_cases hz : IsUnit z.1
  · simp only [localMixedDiagramPair,dite_eq_left hz]
    have he := primePair_eq_localDiagramPair h k hs ks q hq hp hV g hg (hz.unit,z.2)
    simpa only [IsUnit.unit_spec] using he
  · have hz0 : z.1=0 := by simpa only [isUnit_iff_ne_zero,not_not] using hz
    simp only [localMixedDiagramPair,dite_eq_right hz,primePair]
    rw [primeSpectator_zero_of_giant q (g q) hg _ h z.1 z.2 (Or.inl hz0),zero_mul]

end Ostmann.Arithmetic.HistorySignedSpectatorDiagramAverage

end

end OAI
