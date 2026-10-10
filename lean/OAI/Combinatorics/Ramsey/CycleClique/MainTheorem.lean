import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.FiniteRange
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem thm_main :
    (∀ m n : ℤ, n ≤ m → 3 ≤ n → (m, n) ≠ (3, 3) →
      (cycleCliqueRamsey m.toNat n.toNat : ℤ) = (m - 1) * (n - 1) + 1) ∧
    cycleCliqueRamsey 3 3 = 6 := by
  constructor
  · intro m n hmn hn hne
    have hmnN : n.toNat ≤ m.toNat := by omega
    have hnN : 3 ≤ n.toNat := by omega
    have hneN : (m.toNat, n.toNat) ≠ (3, 3) := by
      intro he
      have hm3 := congrArg Prod.fst he
      have hn3 := congrArg Prod.snd he
      have hm3' : m = 3 := by omega
      have hn3' : n = 3 := by omega
      exact hne (by simp [hm3', hn3'])
    have h := main m.toNat n.toNat hmnN hnN hneN
    have hmcast : ((m.toNat - 1 : ℕ) : ℤ) = m - 1 := by omega
    have hncast : ((n.toNat - 1 : ℕ) : ℤ) = n - 1 := by omega
    have hcast := congrArg (fun a : ℕ => (a : ℤ)) h
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, hmcast, hncast] using hcast
  · exact exceptional

end CycleClique

end OAI
