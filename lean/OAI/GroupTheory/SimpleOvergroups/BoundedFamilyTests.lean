import Mathlib
import OAI.GroupTheory.SimpleOvergroups.FirstFamilies
import OAI.GroupTheory.SimpleOvergroups.NamedActions
import OAI.GroupTheory.SimpleOvergroups.ThreeCodes

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open FiniteAlgebraicEnvelopes Bootstrap BoundedEncoding
noncomputable section
open scoped Classical

structure TestCertificate {A S Q : Type*}
    (C : DelimiterCode A S) (f : List A → Part (Option Q)) (n : ℕ) : Prop where
  total : ∀ w, (C.encode w).length ≤ n → (f w).Dom
  nonzero : Search.value f [] ≠ none
  contextual : CodeTable.Contextual C (Search.value f) n
  ideal : CodeTable.ZeroIdeal C (Search.value f) n

namespace TestCertificate
variable {A S Q : Type*} [DecidableEq A] [DecidableEq Q]
  (C : DelimiterCode A S) (f : List A → Part (Option Q)) {n : ℕ}

omit [DecidableEq A] [DecidableEq Q] in
theorem of_value (q : List A → Option Q)
    (hf : ∀ w, (C.encode w).length ≤ n → q w ∈ f w)
    (h0 : q [] ≠ none) (hc : CodeTable.Contextual C q n) (hz : CodeTable.ZeroIdeal C q n) :
    TestCertificate C f n := by
  have he (w : List A) (hw : (C.encode w).length ≤ n) : Search.value f w = q w :=
    Part.mem_unique (Search.value_mem (hf w hw).1) (hf w hw)
  refine ⟨fun w hw => (hf w hw).1, ?_, ?_, ?_⟩
  · rw [he [] (Nat.zero_le _)]
    exact h0
  · intro a b u v hu hv h
    have hlu : (C.encode u).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hu
      omega
    have hlv : (C.encode v).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hv
      omega
    rw [he u hlu,he v hlv] at h
    rw [he _ hu,he _ hv]
    exact hc a b u v hu hv h
  · intro a b u hu h
    have hlu : (C.encode u).length ≤ n := by
      simp only [DelimiterCode.encode_append,List.length_append] at hu
      omega
    rw [he u hlu] at h
    rw [he _ hu]
    exact hz a b u hu h
end TestCertificate

namespace GroupFamily
variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
theorem certificate (C : DelimiterCode (Fin k × Bool) ThreeCodes.Alphabet) (n : ℕ) :
    TestCertificate C (test s) n := by
  apply TestCertificate.of_value C (test s) (fun w => some (WordProblem.testedClass s w))
  · intro w hw; exact Part.mem_some _
  · exact Option.some_ne_none _
  · intro a b u v hu hv h
    exact congrArg some (context s (Option.some.inj h) a b)
  · intro a b u hu h
    cases h
end GroupFamily

namespace ProductFamily
variable {A : Type*} [DecidableEq A] {m n : ℕ} (C : WordCalculus (FreeMonoid A) m)
  (code : DelimiterCode (Letter A) ThreeCodes.Alphabet)
  (cost : A → ℕ) (hc : ∀ w, grade C w = wordCost cost w)
  (hp : ∀ a, 10 * ProductFamily.cost cost a + 2 ≤ (code.block a).length)
  (hm : n / 10 ≤ m) {f : List A → Part (List A)}
  (hf : ∀ u, C.grade (FreeMonoid.ofList u) ≤ n / 10 →
    (C.normal (FreeMonoid.ofList u)).toList ∈ f u)

include hc hp hm hf
theorem certificate : TestCertificate code (test C.omega.toList f) n := by
  have hb (w : List (Letter A)) (hw : (code.encode w).length ≤ n) : grade C w ≤ n / 10 := by
    rw [hc]
    exact code.cost_le_quota _ hp hw
  apply TestCertificate.of_value code (test C.omega.toList f) (value C)
  · intro w hw
    exact test_full C w (hb w hw) hf
  · exact value_nil C
  · intro a b u v hu hv h
    exact value_context C h a b ((hb _ hu).trans hm) ((hb _ hv).trans hm)
  · intro a b u hu h
    exact value_zero_context C h a b ((hb _ hu).trans hm)
end ProductFamily

namespace ActionFamily
open NamedAction
variable {G X V Y K L : Type*} [Group V] [MulAction V Y]
  [DecidableEq G] [DecidableEq X] [DecidableEq K] [DecidableEq L]
  {N : Operations G X} {m n : ℕ} {C : ActionCalculus V Y K L m}
  (I : Interpretation N C) (code : DelimiterCode (Letter G X) ThreeCodes.Alphabet)
  (hp : ∀ a, 10 * N.letterCost a + 2 ≤ (code.block a).length) (hm : 3 * (n / 10) ≤ m)
  (f : List (Letter G X) → Part (Result K L))
  (hf : ∀ w, N.wordCost w ≤ n / 10 → N.totalTest I.gkey I.xkey w ∈ f w)

include I hp hm hf
omit [DecidableEq G] [DecidableEq X] [DecidableEq K] in
theorem certificate : TestCertificate code f n := by
  have hb (w : List (Letter G X)) (hw : (code.encode w).length ≤ n) : N.wordCost w ≤ n / 10 :=
    code.cost_le_quota _ hp hw
  apply TestCertificate.of_value code f (N.totalTest I.gkey I.xkey)
  · intro w hw
    exact hf w (hb w hw)
  · exact I.totalTest_nil
  · intro a b u v hu hv h
    exact I.totalTest_context h (hb _ hu) (hb _ hv) hm
  · intro a b u hu h
    exact I.totalTest_zero_context h (hb _ hu) hm
end ActionFamily
end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
