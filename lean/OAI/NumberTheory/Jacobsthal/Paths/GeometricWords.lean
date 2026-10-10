import OAI.NumberTheory.Jacobsthal.Partitions.PaperGeometricRegularity

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricWordsAudit
open PrimeHistories GeometricRegularWords FirstIsolatedPosition IsolatedRealPrimeRange
open IsolatedBinGeometry LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints


theorem geometric_nonempty {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z) : ps ≠ [] := by
  obtain ⟨p,hp,_⟩ := geometric_isolated_prime hw htop hxi z ps hp
  exact List.ne_nil_of_mem hp

theorem geometric_isolated_range {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hpower : w^B=top) (z : Node) (ps : List ℕ)
    (hp : ps ∈ geometricWords hw htop hxi C B R L alpha beta z)
    (hsearch : w^((1/4:ℝ)) ≤ alpha*B) :
    ∃ pre p tail,ps=pre++p::tail ∧
      top^alpha ≤ lower w top xi (label (zero_lt_one.trans hw) htop hxi p) ∧
      upper w top xi (label (zero_lt_one.trans hw) htop hxi p) ≤ top^beta ∧
      ActualSourceTags.searchBin w (lower w top xi (label (zero_lt_one.trans hw) htop hxi p)) ∧
      ∀ q ∈ pre,¬isolatedBin w top xi B alpha beta (label (zero_lt_one.trans hw) htop hxi q) := by
  obtain ⟨pre,p,tail,he,hisol,hfirst⟩ := geometric_first_isolated hw htop hxi z ps hp
  have hrange := isolated_real_range hw htop hxi hpower hisol
  exact ⟨pre,p,tail,he,hrange.1,hrange.2,isolated_bin_search hisol hsearch,hfirst⟩
end NumberTheoryLean.GeometricWordsAudit


end Erdos970

end OAI
