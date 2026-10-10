import OAI.Computability.BinPacking.Search.ExtensionVerifier
import OAI.Computability.BinPacking.Search.SearchStageMachines

namespace OAI

namespace BinPackingGap

open Turing BinPackingGames.Foundations.Complexity

namespace OptimalSearch

noncomputable def decider (h : PEqualsNP) : List Bool → Bool :=
  Classical.choose (h.inP packingExtension_inNP)

noncomputable def decisionComputation (h : PEqualsNP) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) (fun answer => [answer])
      (decider h) :=
  Classical.choose (Classical.choose_spec (h.inP packingExtension_inNP))

theorem decisionSpec (h : PEqualsNP) :
    MachineFiniteAlphabet.FiniteAlphabet (decisionComputation h).tm ∧
      ∀ input, ExtensionCertificate.language input ↔ decider h input = true :=
  Classical.choose_spec (Classical.choose_spec (h.inP packingExtension_inNP))

theorem decidesExtension (h : PEqualsNP) : SearchSemantics.DecidesExtension (decider h) :=
  SearchOptimalConstruction.decidesExtension_of_language (decisionSpec h).2

end OptimalSearch

noncomputable def absoluteAdditiveAlgorithm_of_pEqualsNP (h : PEqualsNP) :
    AbsoluteAdditiveAlgorithm 0 :=
  SearchOptimalConstruction.ofDecision SearchStageMachines.stages
    (OptimalSearch.decider h) (OptimalSearch.decisionComputation h)
    (OptimalSearch.decisionSpec h).1 (OptimalSearch.decidesExtension h)

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_optimal (h : PEqualsNP)
    (items : RawInstance) (valid : items.Valid) :
    ∃ packing : RawPacking,
      (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits items) =
        some packing ∧ packing.Feasible items ∧ packing.bins = opt (items.toInstance valid) :=
  SearchMachineComposition.algorithm_optimal (OptimalSearch.decidesExtension h) items valid

@[simp] theorem absoluteAdditiveAlgorithm_of_pEqualsNP_empty (h : PEqualsNP) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits []) =
      some ⟨0, []⟩ :=
  SearchMachineComposition.algorithm_empty (OptimalSearch.decider h)

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_malformed (h : PEqualsNP)
    (input : List Bool) (malformed : BinaryEncoding.decodeRawInstance input = none) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run input = none :=
  SearchMachineComposition.algorithm_malformed (OptimalSearch.decider h) input malformed

theorem absoluteAdditiveAlgorithm_of_pEqualsNP_invalid (h : PEqualsNP)
    (items : RawInstance) (invalid : ¬ items.Valid) :
    (absoluteAdditiveAlgorithm_of_pEqualsNP h).run (BinaryEncoding.rawInstanceBits items) = none :=
  SearchMachineComposition.algorithm_invalid (OptimalSearch.decider h) items invalid

end BinPackingGap

end OAI
