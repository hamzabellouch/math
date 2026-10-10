import OAI.Computability.PerfectCompleteness.Machines.PayloadCellsMachine

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Foundations.Complexity.CookLevin.PayloadCellsMachine

open InitializationTemplate WitnessEncoding

local instance alphabetDecidable (V : NPVerifier) : ∀ k, DecidableEq (V.computation.tm.Γ k) :=
  fun _ => Classical.decEq _

def symbolSpec (V : NPVerifier) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) : SymbolSpec :=
  if h : k = V.computation.tm.k₀ then by
    subst k
    exact ⟨true, decide (some (V.computation.inputAlphabet.invFun true) = a),
      decide (some (V.computation.inputAlphabet.invFun false) = a), decide (none = a)⟩
  else ⟨false, false, false, decide (none = a)⟩

def symbolTable (V : NPVerifier) : Fin (VerifierCircuit.indexing V).symbolCount → SymbolSpec :=
  fun j => let symbol := (VerifierCircuit.indexing V).symbols.symm j
    symbolSpec V symbol.1 symbol.2

def payloadRowTokens (V : NPVerifier) (q i : Nat) : List PostfixModel.Token :=
  Row.tokens (symbolTable V) q i

theorem symbolTokens_eq_initialCellTokens (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length)
    (hS : (inputPrefix input).length + i < S) (k : V.computation.tm.K)
    (a : Option (V.computation.tm.Γ k)) :
    symbolTokens (symbolSpec V k a) (V.witnessBound.eval input.length) i =
      initialCellTokens V input S k ⟨(inputPrefix input).length + i, hS⟩ a := by
  by_cases hk : k = V.computation.tm.k₀
  · subst k
    have hp : ¬ (inputPrefix input).length + i < (inputPrefix input).length := by omega
    have hn : (inputPrefix input).length + i - (inputPrefix input).length = i := by omega
    have hcell : inputCellTokens (V.witnessBound.eval input.length) input
        V.computation.inputAlphabet.invFun ((inputPrefix input).length + i) a =
        muxTokens (presenceTokens (V.witnessBound.eval input.length) i)
          (payloadSymbolTokens (V.witnessBound.eval input.length)
            V.computation.inputAlphabet.invFun i a) [.const (decide (none = a))] := by
      simp only [inputCellTokens, ite_eq_right hp, hn, ite_eq_left hi]
    simpa [symbolTokens, symbolSpec, initialCellTokens, payloadTokens, payloadSymbolTokens] using hcell.symm
  · simp [symbolSpec, symbolTokens, initialCellTokens, hk]

theorem payloadRowTokens_eq (V : NPVerifier) (input : List Bool) (S i : Nat)
    (hi : i < V.witnessBound.eval input.length) (hS : (inputPrefix input).length + i < S) :
    payloadRowTokens V (V.witnessBound.eval input.length) i =
      (List.ofFn fun j : Fin (VerifierCircuit.indexing V).symbolCount =>
        let symbol := (VerifierCircuit.indexing V).symbols.symm j
        initialCellTokens V input S symbol.1 ⟨(inputPrefix input).length + i, hS⟩ symbol.2).flatten := by
  rw [payloadRowTokens, Row.tokens_eq_ofFn]
  congr 1
  congr 1
  funext j
  exact symbolTokens_eq_initialCellTokens V input S i hi hS _ _

end UniqueGamesTheorem.Foundations.Complexity.CookLevin.PayloadCellsMachine

end

end

end OAI
