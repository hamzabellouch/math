import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantXiReplacementActualGuardedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesComparisonNorm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistorySignedResidues
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k₀ l : ℕ} {E : Finset ℕ}

def comparisonGuardedPrimeDifference (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ)
    {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hout : ∀ q ∈ outside, q.Prime) (deleted : Finset ℕ)
    (hZ : 0 < logCellMass C.giantCenter deleted) (n : ℕ) : ℂ :=
  letI : NeZero (comparisonModulus h k outside n) :=
    ⟨(comparisonModulus_pos h k hs ks hout n).ne'⟩
  guardedPrimeDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
    (pairModulus_dvd_comparisonModulus h k outside n)

def comparisonGuardedMixedDifference (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ)
    {outside : List ℕ} (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz k₀ L) outside)
    (hout : ∀ q ∈ outside, q.Prime) (deleted : Finset ℕ)
    (hZ : 0 < logCellMass C.giantCenter deleted) (n : ℕ) : ℂ :=
  letI : NeZero (comparisonModulus h k outside n) :=
    ⟨(comparisonModulus_pos h k hs ks hout n).ne'⟩
  guardedMixedDifference C s h k hs ks deleted hZ (comparisonModulus h k outside n)
    (pairModulus_dvd_comparisonModulus h k outside n)

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI
