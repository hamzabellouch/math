import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairNumerators
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSources

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairVariableBAverageNonzero
open Construction Characters.RationalHistory HistoryPairPattern HistoryPairRows
open HistoryPairRepresentatives MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem variable_row_nonzero_of_ancestor_units
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (p : ℕ) [Fact p.Prime] (i : Occurrences h k)
    (hx : AncestorUnits h k (fun j => (v j : ZMod p)) i)
    (hV : ∀ j ≤ l, V j < p) :
    (eval v (leftFlag h k hs ks i) : ZMod p) ≠ 0 ∨
      (eval v (rightFlag h k hs ks i) : ZMod p) ≠ 0 := by
  have hn := flags_nonzero_field h k hs ks i (fun j => (v j : ZMod p)) hx
    (HistoryPairNumerators.frequency_units h k hs ks p hV)
  simpa only [Expr.eval₂_cast_int] using hn

theorem variable_rows_nonzero_at_prime_of_ancestor_units
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (r : Representative h k) (p : ℕ) [Fact p.Prime]
    (hx : ∀ i : Fiber h k r, AncestorUnits h k (fun j => (v j : ZMod p)) i.val)
    (hV : ∀ j ≤ l, V j < p) :
    ∀ i : Fiber h k r,
      (eval v (leftFlag h k hs ks i.val) : ZMod p) ≠ 0 ∨
        (eval v (rightFlag h k hs ks i.val) : ZMod p) ≠ 0 := by
  intro i
  exact variable_row_nonzero_of_ancestor_units h k hs ks v p i.val (hx i) hV

theorem variable_rows_nonzero_of_ancestor_units
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (r : Representative h k)
    (hx : ∀ i : Fiber h k r,
      AncestorUnits h k (fun j => (v j : ZMod (prime h k r))) i.val)
    (hV : ∀ j ≤ l, V j < prime h k r) :
    ∀ i : Fiber h k r,
      (eval v (leftFlag h k hs ks i.val) : ZMod (prime h k r)) ≠ 0 ∨
        (eval v (rightFlag h k hs ks i.val) : ZMod (prime h k r)) ≠ 0 := by
  let : Fact (prime h k r).Prime := ⟨representative_prime h k hs ks r⟩
  exact variable_rows_nonzero_at_prime_of_ancestor_units h k hs ks v r
    (prime h k r) hx hV

open CanonicalOccurrenceTransport HistorySymbolicEncoding HistoryPairRepresentativeVariables
open HistoryPairKernelReplacement
variable {d : Decomposition} {Bs BD Bz : ℝ} {depth : ℕ} {L : ℝ} {E : Finset ℕ}

theorem variable_rows_nonzero_of_source_samples
    (C : InitialSourceChoice d Bs BD Bz depth L E)
    {spectator : PrimeSource} (hsep : C.CrossRoleSeparation spectator)
    (h k : History l)
    (hh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) h)
    (kh : TreeSourceLabels (Template.initial (2*(Conclusion.bulkSize depth L/2)) depth) k)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (v : PairKey h k → ℤ) (hv : SmallSourceSamples C.sources h k v)
    (r : Representative h k) (p : ℕ) (hp : p.Prime)
    (hr : v (representativeMap h k r) = (p : ℤ))
    (hV : ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (V j)) :
    ∀ i : Fiber h k r,
      (eval v (leftFlag h k hs ks i.val) : ZMod p) ≠ 0 ∨
        (eval v (rightFlag h k hs ks i.val) : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  apply variable_rows_nonzero_at_prime_of_ancestor_units h k hs ks v r p
  · intro i
    apply new_sample_ancestor_units C hsep h k hh kh hs ks v hv i.val p hp
    simpa only [i.property] using hr
  · exact new_sample_frequency_bound C.sources h k v hv r p hr hV

end Ostmann.Arithmetic.HistoryPairVariableBAverageNonzero

end

end OAI
