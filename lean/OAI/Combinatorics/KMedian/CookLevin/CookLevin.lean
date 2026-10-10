import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.TableauEndpoints
import OAI.Combinatorics.KMedian.Hardness.Classes

namespace OAI

section Inline_PCPCookLevin

namespace MetricKMedian.PCP.CookLevin
open Turing Turing.TM2 Function Finset
open Complexity Tableau
open scoped Classical

lemma polynomial_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
variable [∀ k, Fintype (P.tm.Γ k)]
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
def firstWord (x : Word) : Word := encodeNat x.length++x
def inputPrefix (x : Word) : List (P.tm.Γ P.tm.k₀) := (firstWord x).map P.inputAlphabet.invFun
def inputSize (x : Word) : ℕ := (firstWord x).length+p.eval x.length
def time (x : Word) : ℕ := P.time.eval (inputSize p x)
noncomputable def space (x : Word) : ℕ := inputSize p x+radius P.tm.m*time P p x+1
noncomputable def boundary (x : Word) : Boundary (Γ := P.tm.Γ) (Λ := P.tm.Λ) (σ := P.tm.σ) where
  firstControl := (some P.tm.main,P.tm.initialState)
  firstPrefix := (initList P.tm (inputPrefix P x)).stk
  certificateBound k := if k=P.tm.k₀ then p.eval x.length else 0
  last := haltList P.tm [P.outputAlphabet.invFun true]
noncomputable def system (x : Word) := boundedSystem P.tm.m (boundary P p x) (time P p x) (space P p x)

omit [∀ k, Fintype (P.tm.Γ k)] in
lemma last_length (x : Word) (k : P.tm.K) : ((boundary P p x).last.stk k).length ≤ space P p x := by
  dsimp only [boundary,haltList]
  split_ifs with hk
  · subst k
    change 1 ≤ space P p x
    unfold space
    omega
  · exact Nat.zero_le _
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma init_length (w : Word) (x : Word) (hw : w.length ≤ p.eval x.length) (k : P.tm.K) :
    ((initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk k).length ≤ inputSize p x := by
  dsimp only [initList]
  split_ifs with hk
  · subst k
    simpa [initList,encodePair,inputSize,firstWord,Nat.add_assoc] using Nat.add_le_add_left hw ((encodeNat x.length).length+x.length)
  · exact Nat.zero_le _
omit [∀ k, Fintype (P.tm.Γ k)] in
lemma initial_prefix (w : Word) (x : Word) (hw : w.length ≤ p.eval x.length) (k : P.tm.K) :
    ∃ z, z.length ≤ (boundary P p x).certificateBound k ∧
      ((initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk k)=(boundary P p x).firstPrefix k++z := by
  by_cases hk : k=P.tm.k₀
  · subst k
    refine ⟨w.map P.inputAlphabet.invFun,?_,?_⟩
    · simpa [boundary] using hw
    · simp [boundary,initList,inputPrefix,firstWord,encodePair,List.map_append]
  · refine ⟨[],by simp [boundary,hk],?_⟩
    simp [initList,boundary,hk]

lemma complete (x w : Word) (hw : w.length ≤ p.eval x.length) (hv : verify (x,w)=true) :
    ∃ a, (system P p x).Satisfies a := by
  let c := initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)
  apply path_complete P.tm.m (boundary P p x) (time P p x) (space P p x) c
  · intro k
    have hh := init_length P p w x hw k
    change (c.stk k).length ≤ inputSize p x at hh
    dsimp only [space]
    omega
  · rfl
  · exact initial_prefix P p w x hw
  · have ht := P.outputsFun (x,w)
    have hn : (encodePair (x,w)).length ≤ inputSize p x := by
      simp only [encodePair,inputSize,firstWord,List.length_append]
      omega
    have htime := polynomial_mono P.time hn
    have out : StateTransition.EvalsToInTime (step P.tm.m) c (some (boundary P p x).last) (time P p x) := by
      have out := (show StateTransition.EvalsToInTime (step P.tm.m)
        (initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun))
        (some (haltList P.tm ((encodeBit (verify (x,w))).map P.outputAlphabet.invFun)))
        (time P p x) from ⟨ht.toEvalsTo,ht.steps_le_m.trans htime⟩)
      simpa [c,boundary,encodeBit,hv] using out
    apply run_of_outputs P.tm.m out rfl

omit [∀ k, Fintype (P.tm.Γ k)] in
lemma initial_decode (x : Word) (c : Cfg P.tm.Γ P.tm.Λ P.tm.σ)
    (hc : (c.l,c.var)=(boundary P p x).firstControl)
    (hw : ∀ k, ∃ z, z.length ≤ (boundary P p x).certificateBound k ∧ c.stk k=(boundary P p x).firstPrefix k++z) :
    ∃ w : Word, w.length ≤ p.eval x.length ∧ c=initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun) := by
  obtain ⟨z,hz,hs⟩ := hw P.tm.k₀
  let w := z.map P.inputAlphabet
  have hwlen : w.length ≤ p.eval x.length := by simpa [boundary,w] using hz
  refine ⟨w,hwlen,?_⟩
  have hstk : c.stk=(initList P.tm ((encodePair (x,w)).map P.inputAlphabet.invFun)).stk := by
    funext k
    by_cases hk : k=P.tm.k₀
    · subst k
      simpa [boundary,initList,inputPrefix,firstWord,encodePair,w,List.map_append,List.map_map,Function.comp_def] using hs
    · obtain ⟨z,hz,hs⟩ := hw k
      have he : z=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by simpa [boundary,hk] using hz))
      simpa [boundary,initList,hk,he] using hs
  cases c with
  | mk l v stk =>
    change (l,v)=(some P.tm.main,P.tm.initialState) at hc
    cases congrArg Prod.fst hc
    cases congrArg Prod.snd hc
    cases hstk
    rfl

lemma sound (x : Word) (ha : ∃ a, (system P p x).Satisfies a) :
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true := by
  obtain ⟨a,ha⟩ := ha
  obtain ⟨c,hc,hcert,he⟩ := bounded_sound P.tm.m (boundary P p x) (time P p x) (space P p x) a ha (last_length P p x)
  obtain ⟨w,hlen,rfl⟩ := initial_decode P p x c hc hcert
  refine ⟨w,hlen,?_⟩
  have ht := (P.outputsFun (x,w)).toEvalsTo
  have hi := Padded.agrees (step P.tm.m) _ (boundary P p x).last
    (haltList P.tm ((encodeBit (verify (x,w))).map P.outputAlphabet.invFun)) (time P p x)
    (by simpa only [advance_eq_padded] using he) rfl rfl ht
  have hh := congrArg (fun c : Cfg P.tm.Γ P.tm.Λ P.tm.σ => c.stk P.tm.k₁) hi
  simpa [boundary,haltList,encodeBit] using (congrArg (List.map P.outputAlphabet) hh).symm
lemma correct (x : Word) : (∃ a, (system P p x).Satisfies a) ↔
    ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x,w)=true :=
  ⟨sound P p x,fun ⟨w,hw,hv⟩ => complete P p x w hw hv⟩
end MetricKMedian.PCP.CookLevin

end Inline_PCPCookLevin

end OAI
