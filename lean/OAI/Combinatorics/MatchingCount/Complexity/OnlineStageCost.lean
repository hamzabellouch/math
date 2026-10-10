import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.OnlineGuard
import OAI.Combinatorics.MatchingCount.Complexity.OnlineRequestCost

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial NumericBounds

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma work_precompose {f : A→B} {g : B→Experiment C} {F : TreeTyped.Realizer f} {G : Realizer g}
    {m : A→ℕ} {n : B→ℕ} (hF : TreeTyped.WorkBound F m) (hG : WorkBound G n)
    (h : Bound (n ∘ f) m) : WorkBound (composition (deterministic F) G) m := by
  obtain ⟨p,hp⟩:=h
  exact work_composition (work_deterministic hF) hG p (fun a=>hp a)
lemma work_from_weight {f : A→Experiment B} {F : Realizer f} {m : A→ℕ}
    (hF : PolynomialTime F) (h : Bound weight m) : WorkBound F m := by
  obtain ⟨p,hp⟩:=h
  exact work_of_polynomial hF p hp
end MatchingFPRAS.OnlineTree

namespace MatchingFPRAS.OnlineStage
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSample

def inputSize (x : Input) : ℕ := repeatMeasure requestMeasure x.2+weight x
lemma work_execute : OnlineTree.WorkBound executeRealizer inputSize := by
  unfold executeRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial
  · apply OnlineTree.work_pair _ _ X (fun x=>by simp [inputSize])
    · apply OnlineTree.work_deterministic
      exact work_of_polynomial polynomial_first X (fun x=>by simp [inputSize])
    · apply OnlineTree.work_precompose
        (work_of_polynomial polynomial_second X (fun x=>by simp [inputSize])) work_many
      exact of_le (fun x=>by simp only [Function.comp_apply]; unfold inputSize;omega)
  · exact OnlineTree.work_deterministic ExecutableSource.polynomial_sparseStage
end MatchingFPRAS.OnlineStage

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

def stateSize (x : State) : ℕ := requestSize x.1+weight x
lemma weight_le_stateSize (x : State) : weight x ≤ stateSize x := by unfold stateSize;omega
lemma bound_prepare : Bound (OnlineStage.inputSize ∘ prepare) requestSize := by
  have hw:=NumericBounds.weight (work_of_polynomial polynomial_prepare X
    (fun x=>by simpa using weight_le_requestSize x))
  have hs : Bound (fun x : RequestInput=>x.2) requestSize := of_le (fun x=>by unfold requestSize;omega)
  have hm:=bound_sourceRequest
  exact add (add (add hs (mono hw (fun x=>weight_snd (prepare x)))) hm) hw
lemma work_step : OnlineTree.WorkBound stepRealizer stateSize := by
  unfold stepRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial
  · apply OnlineTree.work_pair _ _ X (fun x=>by simpa using weight_le_stateSize x)
    · apply OnlineTree.work_deterministic
      exact work_of_polynomial polynomial_identity X (fun x=>by simpa using weight_le_stateSize x)
    · apply OnlineTree.work_precompose
        (work_of_polynomial (polynomial_composition polynomial_first polynomial_prepare) X
          (fun x=>by simpa using weight_le_stateSize x)) OnlineStage.work_execute
      exact NumericBounds.comp (f:=Prod.fst) (g:=OnlineStage.inputSize ∘ prepare) bound_prepare
        (of_le (fun x=>by simp only [Function.comp_apply]; unfold stateSize;omega))
  · exact OnlineTree.work_deterministic polynomial_carry
lemma work_body : OnlineTree.WorkBound bodyRealizer (fun x=>stateSize x.2+weight x) := by
  unfold bodyRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_precompose
    (work_of_polynomial polynomial_second X (fun x=>by simp)) work_step
  exact of_le (fun x=>by dsimp;omega)
end MatchingFPRAS.OnlineTrial

namespace MatchingFPRAS.OnlineGuard
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

lemma bound_testRequest : Bound (fun x : RequestInput=>repeatMeasure requestMeasure (16,sourceRequest x)) requestSize := by
  have hw := NumericBounds.weight (work_of_polynomial polynomial_sourceRequest X
    (fun x=>by simpa using weight_le_requestSize x))
  simp only [repeatMeasure,weight_prod]
  exact add (add (const 16 _) (add (const (1+weight (16:ℕ)) _) hw)) bound_sourceRequest
lemma work_test : OnlineTree.WorkBound testRealizer requestSize := by
  unfold testRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial
  · apply OnlineTree.work_pair _ _ X (fun x=>by simpa using weight_le_requestSize x)
    · exact OnlineTree.work_deterministic (work_of_polynomial polynomial_first X
        (fun x=>by simpa using weight_le_requestSize x))
    · exact OnlineTree.work_precompose (work_of_polynomial
        (polynomial_pair (polynomial_constant _) polynomial_sourceRequest) X
        (fun x=>by simpa using weight_le_requestSize x)) work_many bound_testRequest
  · exact OnlineTree.work_deterministic polynomial_accept
lemma work_checked : OnlineTree.WorkBound checkedRealizer OnlineTrial.stateSize := by
  unfold checkedRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial
  · apply OnlineTree.work_pair _ _ X (fun x=>by simpa using OnlineTrial.weight_le_stateSize x)
    · exact OnlineTree.work_deterministic (work_of_polynomial polynomial_second X
        (fun x=>by simpa using OnlineTrial.weight_le_stateSize x))
    · exact OnlineTree.work_precompose (work_of_polynomial polynomial_first X
        (fun x=>by simpa using OnlineTrial.weight_le_stateSize x)) work_test
        (of_le (fun x=>by simp only [Function.comp_apply]; unfold OnlineTrial.stateSize;omega))
  · exact OnlineTree.work_deterministic polynomial_finish
end MatchingFPRAS.OnlineGuard

end OAI
