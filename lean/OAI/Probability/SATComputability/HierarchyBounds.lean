import OAI.Probability.SATComputability.HierarchyEncoding
import OAI.Probability.SATComputability.FiniteEnumeration

namespace OAI

namespace FixedClauseThreshold.Computability

open Encodable Denumerable Nat.Partrec

theorem branchEntry_code_le (c : Code) : encode (branchEntry c).2 ≤ encode c := by
  cases c with
  | comp w c => exact (Code.encode_lt_comp w c).2.le
  | zero => rfl
  | succ => exact Nat.zero_le _
  | left => exact Nat.zero_le _
  | right => exact Nat.zero_le _
  | pair c d => exact Nat.zero_le _
  | prec c d => exact Nat.zero_le _
  | rfind' c => exact Nat.zero_le _

theorem rawBranches_code_le (c : Code) :
    ∀ b ∈ rawBranches c, encode b.2 ≤ encode c := by
  induction c with
  | pair c d _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with h | h
    · subst b
      exact (branchEntry_code_le c).trans (Code.encode_lt_pair c d).1.le
    · exact (ih b h).trans (Code.encode_lt_pair c d).2.le
  | zero | succ | left | right | comp _ _ _ _ | prec _ _ _ _ | rfind' _ _ =>
    simp only [rawBranches, List.not_mem_nil, false_implies, implies_true]

theorem normalizedBranches_code_le (c : Code) :
    ∀ b ∈ normalizedBranches c, encode b.2 ≤ encode c := by
  dsimp only [normalizedBranches]
  split_ifs
  · intro b hb
    have h : b = (1, Code.zero) := by simpa only [List.mem_singleton] using hb
    subst b
    exact Nat.zero_le _
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    exact rawBranches_code_le c x hx

def codeAlphabet (bound : ℕ) : List Code :=
  (List.range (bound+1)).map (ofNat Code)

theorem mem_codeAlphabet (bound : ℕ) (c : Code) :
    c ∈ codeAlphabet bound ↔ encode c ≤ bound := by
  constructor
  · intro h
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h
    simpa only [List.mem_range, encode_ofNat, Nat.lt_succ_iff] using hn
  · intro h
    exact List.mem_map.mpr ⟨encode c, List.mem_range.mpr (Nat.lt_succ_iff.mpr h), ofNat_encode c⟩

def hierarchyStates (bound labels : ℕ) : List (List Code) := words (codeAlphabet bound) labels

theorem mem_hierarchyStates (bound labels : ℕ) (cs : List Code) :
    cs ∈ hierarchyStates bound labels ↔
      cs.length = labels ∧ ∀ c ∈ cs, encode c ≤ bound := by
  simp only [hierarchyStates, mem_words, mem_codeAlphabet]

end FixedClauseThreshold.Computability

end OAI
