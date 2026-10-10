import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram
import OAI.Combinatorics.ContingencyTables.Machines.LiteralProgram

namespace OAI

/-! # The greedy initializer on the public binary tape -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS Turing
open scoped BigOperators

private lemma encodeNat_nonzero (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠0 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

private lemma encodeNat_alphabet (n : ℕ) (a : Symbol) (ha : a∈encodeNat n) : a≠6 ∧ a≠7 := by
  simp only [encodeNat,List.mem_append,List.mem_map,List.mem_singleton] at ha
  rcases ha with ⟨b,_,rfl⟩|rfl
  · cases b <;> decide
  · decide

lemma publicGreedy_alphabet (as : List Symbol) :
    ∀ a∈publicGreedy as,a≠6 ∧ a≠7 := by
  intro a ha
  obtain ⟨row,_,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  exact encodeNat_alphabet n a ha

lemma encodeMargins_nonzero {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    ∀ a∈Algorithms.encodeMargins r c,a≠0 := by
  rw [encodeMargins_natWords]
  intro a ha
  obtain ⟨n,_,ha⟩ := List.mem_flatMap.mp ha
  exact encodeNat_nonzero n a ha

/-- A single finite transition table performs the feasible initialization
from the public margin encoding, with polynomial cost in its bit length. -/
theorem publicGreedy_machine :
    ∃ (A : RandomMachine) (p : Polynomial ℕ),
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ∀ t,
      p.eval (Algorithms.encodeMargins r c).length ≤ t → ∀ bits : Fin t → Bool,
      ∃ X : Table r c,Algorithms.OutputsTable A (Algorithms.encodeMargins r c) bits X.val := by
  obtain ⟨A,p,hp⟩ := LiteralProgram.deterministic_compiles publicGreedyRealizer
    polynomial_publicGreedy publicGreedy_alphabet
  refine ⟨A,p,?_⟩
  intro m n r c ht t htime bits
  refine ⟨table r c ht,?_⟩
  have h := hp (Algorithms.encodeMargins r c) (encodeMargins_nonzero r c) t htime bits
  simpa only [Algorithms.OutputsTable,publicGreedy_spec,table] using h

/-- The same initializer accepts the precision parameter on sampling inputs. -/
theorem publicGreedy_sampling_machine :
    ∃ (A : RandomMachine) (p : Polynomial ℕ),
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ∀ k t,
      p.eval (Algorithms.encodeSamplingInput r c k).length ≤ t → ∀ bits : Fin t → Bool,
      ∃ X : Table r c,Algorithms.OutputsTable A (Algorithms.encodeSamplingInput r c k) bits X.val := by
  obtain ⟨A,p,hp⟩ := LiteralProgram.deterministic_compiles publicGreedyRealizer
    polynomial_publicGreedy publicGreedy_alphabet
  refine ⟨A,p,?_⟩
  intro m n r c ht k t htime bits
  have hnonzero : ∀ a∈Algorithms.encodeSamplingInput r c k,a≠0 := by
    intro a ha
    rcases List.mem_append.mp ha with hm|hk
    · exact encodeMargins_nonzero r c a hm
    · exact encodeNat_nonzero k a hk
  refine ⟨table r c ht,?_⟩
  have h := hp (Algorithms.encodeSamplingInput r c k) hnonzero t htime bits
  simpa only [Algorithms.OutputsTable,publicGreedy_sampling,table] using h

end ContingencyTables.GreedyFeasibleTable

end OAI
