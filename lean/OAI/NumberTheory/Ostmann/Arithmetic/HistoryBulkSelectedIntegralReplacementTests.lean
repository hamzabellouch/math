import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReplacementGeometry
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkResidueRootAverage

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement
open Construction HistoryBulkResidueRootAverage HistoryBulkReplacementGeometry HistoryFrequencyResidues

def rootTest (independent mixed : Bool) (d : Decomposition) {l m : ℕ} {V : ℕ→ℕ}
    {outside : List ℕ} (h g : History l) (hs : h.Supported V outside)
    (gs : g.Supported V outside) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q) (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ) :
    (Fin (2^l)×Fin m→(ZMod (bulkModulus h g outside K))ˣ)→ℂ :=
  if independent then
    if mixed then independentMixed d h g hs gs hp hV σ K
    else independentUnit d h g hs gs hp hV σ K
  else
    if mixed then canonicalMixed d h g hs gs hp hV σ K
    else canonicalUnit d h g hs gs hp hV σ K

theorem sum_norm_rootTest_le (independent mixed : Bool) (d : Decomposition)
    {l m : ℕ} {V : ℕ→ℕ} {outside : List ℕ} (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hp : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q)
    (σ : Equiv.Perm (Fin (2^l)×Fin m)) (K : ℕ) [NeZero (bulkModulus h g outside K)] :
    (∑x,‖rootTest independent mixed d h g hs gs hp hV σ K x‖) ≤
      (bulkModulus h g outside K:ℝ)^(2^l*m+2^(l+1)) := by
  cases independent <;> cases mixed
  · exact sum_norm_canonicalUnit_le d h g hs gs hp hV σ K
  · exact sum_norm_canonicalMixed_le d h g hs gs hp hV σ K
  · exact sum_norm_independentUnit_le d h g hs gs hp hV σ K
  · exact sum_norm_independentMixed_le d h g hs gs hp hV σ K

end Ostmann.Arithmetic.HistoryBulkSelectedIntegralReplacement

end

end OAI
