import OAI.NumberTheory.Ostmann.Supply.TailSieveEnergy

namespace OAI

/-! # The natural-sum and reflected-integer forms of the same sparse weight -/
namespace Ostmann
open scoped Classical BigOperators

theorem summandTail_sparse_pair_sum {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (A B : Set ℕ) (lo X : ℕ) :
    (∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X,
      sparseSubsetWeight p S K (fun i => (a : ZMod (p i)) - (b : ZMod (p i)))) =
    ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
      sparseSubsetWeight p S K (fun i => ((a + b : ℕ) : ZMod (p i))) := by
  have hh := summandTail_pair_sum A B lo X
    (fun z => sparseSubsetWeight p S K (fun i => (z : ZMod (p i))))
  simpa only [Int.cast_sub, Int.cast_natCast] using hh

theorem summandTail_sparse_coverage {n : ℕ} (p : Fin n → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) (A B : Set ℕ) (lo X : ℕ) (c L : ℝ)
    (hlog : Real.log (X : ℝ) = L)
    (hc : c ≤ Real.log X * ∑ a ∈ summandTail A lo X, ∑ b ∈ summandTail B lo X,
      sparseSubsetWeight p S K (fun i => ((a + b : ℕ) : ZMod (p i)))) :
    c ≤ L * ∑ a ∈ positiveSummandTail A lo X, ∑ b ∈ negativeSummandTail B lo X,
      sparseSubsetWeight p S K (fun i => (a : ZMod (p i)) - (b : ZMod (p i))) := by
  have he := congrArg (fun x : ℝ => L * x) (summandTail_sparse_pair_sum p S K A B lo X)
  rw [hlog] at hc
  exact hc.trans_eq he.symm

end Ostmann

end OAI
